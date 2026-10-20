#!/usr/bin/env python3
"""Price retained method/body dependency walls; never admit or execute C++."""

import argparse
import collections
import hashlib
import json
import pathlib
import sys

from compare_ast import (POINTER_PATTERN, publish_report, refuse_numeric_token,
                         refuse_output_alias, unique_object)

FORMAT = "cpp-method-closure-pricing-1"
SCHEMA = "cpp-canonical-probe-0.3"
PROFILE = "integral-callables-and-records-2026-10-20"
BASELINE_MODEL_SHA256 = {
    "LeanModels/Cpp/Callable.lean": "02f4bd5f4f0ef893dc71f3d873f68b12463711faa160b82c1f0498d3e59c17ef",
    "LeanModels/Cpp/LocalFunction.lean": "5770fe7362733d160f82c85c26af814165929f853d0a79343f1cf5eaca1e731f",
    "LeanModels/Cpp/AutomaticDeclarations.lean": "3ac2add160cbea5f33eedc761e2e4b34542364c6bda6db11d5ab958e70ba5dfb",
    "LeanModels/Cpp/RecordEvidence.lean": "34b168582d20a165482a3dbf752e40802b4eb60d9109d813f0ca18ef9a3d3e77"
}

FUNCTIONS = frozenset(("FunctionDecl", "CXXMethodDecl", "CXXConstructorDecl",
                       "CXXDestructorDecl", "CXXConversionDecl"))
BODIES = frozenset(("CompoundStmt", "CXXTryStmt"))
INTEGRALS = frozenset(("bool", "char", "signed char", "unsigned char", "short",
    "unsigned short", "int", "unsigned int", "long", "unsigned long",
    "long long", "unsigned long long"))
BASE_KINDS = frozenset(("BinaryOperator", "BreakStmt", "CXXBoolLiteralExpr", "CaseStmt",
    "CompoundAssignOperator", "CompoundStmt", "ConditionalOperator", "ConstantExpr",
    "ContinueStmt", "DeclRefExpr", "DefaultStmt", "DoStmt", "ExprWithCleanups", "ForStmt",
    "IfStmt", "ImplicitCastExpr", "IntegerLiteral", "NullStmt", "ParenExpr", "ReturnStmt",
    "SwitchStmt", "UnaryOperator", "WhileStmt", "DeclStmt", "VarDecl", "InitListExpr",
    "CXXScalarValueInitExpr"))
BINARY = frozenset(("+", "-", "*", "/", "%", "<<", ">>", "&", "|", "^", "==", "!=",
                    "<", "<=", ">", ">=", "&&", "||", ",", "="))
UNARY = frozenset(("+", "-", "~", "!", "++", "--"))
CASTS = frozenset(("LValueToRValue", "NoOp", "IntegralToBoolean", "IntegralCast"))
CALLS = frozenset(("CallExpr", "CXXMemberCallExpr", "CXXOperatorCallExpr"))
TRANSPARENT = frozenset(("ImplicitCastExpr", "ParenExpr"))
# Snapshot receiver scenarios remove exactly these obligations, never arbitrary
# unsupported nodes/types. The baseline still reports every removed obligation.
RECEIVER = frozenset(("receiver:instance", "node:CXXThisExpr", "node:MemberExpr"))
SNAPSHOT = RECEIVER | frozenset(("record:nonaggregate", "record:user-destructor",
    "record:nontrivial-destruction", "record:initializer", "record:unused-nonintegral-field"))
DIRECT_CALL = frozenset(("call:direct", "cast:FunctionToPointerDecay"))


def verify_baseline(root=None):
    root = pathlib.Path(root) if root is not None else pathlib.Path(__file__).resolve().parents[2]
    for name, expected in BASELINE_MODEL_SHA256.items():
        if hashlib.sha256((root / name).read_bytes()).hexdigest() != expected:
            raise ValueError("pricing baseline changed; review profile against " + name)


def handle(value):
    return isinstance(value, str) and POINTER_PATTERN.fullmatch(value) is not None


def identifier_name(value):
    return isinstance(value, str) and value.isascii() and value.isidentifier()


def inner_walk(root):
    """Every root/inner occurrence, including repeated IDs; no reference stubs."""
    pending = [((), root)]
    while pending:
        path, node = pending.pop()
        if not isinstance(node, dict):
            raise ValueError("AST inner node must be an object")
        yield path, node
        children = node.get("inner", [])
        if not isinstance(children, list):
            raise ValueError("AST inner must be an array")
        pending.extend((path + (i,), child) for i, child in reversed(list(enumerate(children))))


def integral(type_, reference=False):
    if not isinstance(type_, dict):
        return False
    kind = type_.get("kind")
    if reference and kind == "lvalue-reference":
        return integral(type_.get("referent"))
    if kind == "qualified":
        return type(type_.get("const")) is bool and type_.get("volatile") is False and integral(type_.get("base"))
    return kind == "builtin" and type_.get("name") in INTEGRALS


def unqualified(type_):
    while isinstance(type_, dict) and type_.get("kind") == "qualified":
        type_ = type_.get("base")
    return type_ if isinstance(type_, dict) else {}


def effectful(node):
    return any(n.get("kind") in CALLS or n.get("kind") in {"CXXConstructExpr", "CXXNewExpr", "CXXDeleteExpr"}
        or n.get("kind") == "CompoundAssignOperator" or n.get("opcode") in {"=", "++", "--"}
        for _, n in inner_walk(node))


def rank(sets):
    present, sole = collections.Counter(), collections.Counter()
    intersections = collections.Counter()
    for walls in sets:
        walls = tuple(sorted(walls))
        present.update(walls)
        if len(walls) == 1:
            sole.update(walls)
        intersections[walls] += 1
    return {"clear": intersections.get((), 0),
        "walls": [{"wall": key, "present": count, "sole": sole[key]}
                  for key, count in sorted(present.items(), key=lambda row: (-sole[row[0]], -row[1], row[0]))],
        "sets": [{"walls": list(walls), "bodies": count} for walls, count in sorted(intersections.items())]}


class Probe:
    def __init__(self, document):
        if not isinstance(document, dict) or set(document) != {"ast", "metadata"}:
            raise ValueError("expected complete ast/metadata probe envelope")
        self.metadata = document["metadata"]
        if not isinstance(self.metadata, dict) or self.metadata.get("schema_version") != SCHEMA:
            raise ValueError("expected canonical probe schema " + SCHEMA)
        self.nodes = list(inner_walk(document["ast"]))
        if document["ast"].get("kind") != "TranslationUnitDecl" or not handle(document["ast"].get("id")):
            raise ValueError("expected TranslationUnitDecl")
        self.raw = collections.defaultdict(list)
        for path, node in self.nodes:
            if handle(node.get("id")):
                self.raw[node["id"]].append((path, node))
        self.rows = self.index("declarations", "id")
        for key, api in (("type_evidence", "Clang::QualType structured type projection v1"),
                         ("expression_types", "Clang::Expr type projection v1"),
                         ("variable_evidence", "Clang::VarDecl storage and initializer projection v1")):
            if self.metadata.get(key + "_api") != api:
                raise ValueError("missing or unsupported " + key + " supplement")
        self.types = self.index("type_evidence", "occurrence")
        self.expressions = self.index("expression_types", "occurrence")
        self.variables = self.index("variable_evidence", "occurrence")
        self.functions = [(path, node, body) for path, node in self.nodes
            if node.get("kind") in FUNCTIONS for body in node.get("inner", []) if body.get("kind") in BODIES]
        self.by_canonical = collections.defaultdict(list)
        for ordinal, (_, node, _) in enumerate(self.functions):
            walls = set()
            canonical = self.get(self.rows, node.get("id"), "canonical", walls, "declaration")
            if handle(canonical):
                self.by_canonical[canonical].append(ordinal)

    def index(self, name, key):
        rows = self.metadata.get(name)
        if not isinstance(rows, list):
            raise ValueError("expected " + name + " array")
        result = collections.defaultdict(list)
        for row in rows:
            if not isinstance(row, dict) or not handle(row.get(key)):
                raise ValueError("invalid " + name + " row handle")
            result[row[key]].append(row)
        return result

    @staticmethod
    def get(index, identifier, key, walls, label):
        rows = index.get(identifier, [])
        if not rows or any(key not in row for row in rows):
            walls.add("evidence:missing-" + label + ":" + key)
            return None
        first = rows[0][key]
        if any(type(row[key]) is not type(first) or row[key] != first for row in rows):
            walls.add("evidence:conflicting-" + label + ":" + key)
            return None
        return first

    def decl(self, identifier, key, walls):
        return self.get(self.rows, identifier, key, walls, "declaration")

    def type_of(self, identifier, walls, expression=False):
        table = self.expressions if expression else self.types
        return self.get(table, identifier, "type", walls, "expression-type" if expression else "type")

    def canonical(self, identifier, walls):
        canonical = self.decl(identifier, "canonical", walls)
        if not handle(canonical) or not self.rows.get(canonical):
            walls.add("evidence:absent-canonical-declaration")
            return None
        return canonical

    def scopes(self, identifier, walls, include_self=False):
        """Observe both context chains; Lean retains ancestry/identity validation."""
        for context in ("lexical_context", "semantic_context"):
            current = identifier if include_self else self.decl(identifier, context, walls)
            if current is None:
                walls.add("scope:missing-context")
            seen = set()
            while current is not None:
                if not handle(current):
                    walls.add("scope:invalid-context-handle")
                    break
                if current in seen:
                    walls.add("scope:context-cycle")
                    break
                seen.add(current)
                kind = self.decl(current, "kind", walls)
                for key in ("implicit", "dependent_context"):
                    if self.decl(current, key, walls) is not False:
                        walls.add("scope:" + key)
                if self.decl(current, "owning_module", walls) is not None:
                    walls.add("scope:module")
                if kind == "TranslationUnitDecl":
                    break
                if kind not in {"NamespaceDecl", "CXXRecordDecl"}:
                    walls.add("scope:unsupported-context:" + str(kind))
                else:
                    if not identifier_name(self.decl(current, "name", walls)):
                        walls.add("scope:unsupported-name")
                    if kind == "NamespaceDecl":
                        for key in ("inline_namespace", "anonymous_namespace"):
                            if self.decl(current, key, walls) is not False:
                                walls.add("scope:" + key)
                    else:
                        if self.decl(current, "injected_class_name", walls) is not False:
                            walls.add("scope:injected-class")
                        if self.decl(current, "described_template_api", walls) != "CXXRecordDecl.getDescribedClassTemplate":
                            walls.add("evidence:scope-template-api")
                        specialization = self.decl(current, "template_specialization_kind", walls)
                        if self.decl(current, "described_template", walls) is not None or type(specialization) is not int or specialization != 0:
                            walls.add("scope:template-record")
                following = self.decl(current, context, walls)
                if following is None:
                    walls.add("scope:context-does-not-reach-translation-unit")
                current = following

    def ownership(self, identifier, sources, capture_dir):
        walls = set()
        api = self.decl(identifier, "source_origin_api", walls)
        origin = self.decl(identifier, "source_origin", walls)
        if api != "SourceManager expansion/spelling file locations v1" or walls or not isinstance(origin, dict):
            raise ValueError("missing/conflicting declaration physical source origin")
        if not {"expansion", "spelling"}.issubset(origin):
            raise ValueError("missing physical source origin component")
        files = []
        for location in (origin.get("expansion"), origin.get("spelling")):
            if location is None:
                files.append(None)
                continue
            if not isinstance(location, dict) or not isinstance(location.get("file"), str) or not location["file"] or type(location.get("offset")) is not int or location["offset"] < 0:
                raise ValueError("malformed physical source origin")
            file = pathlib.Path(location["file"])
            try:
                files.append((file if file.is_absolute() else capture_dir / file).resolve(strict=True))
            except OSError:
                files.append(None)
        if None in files:
            return "unknown-origin"
        selected = [file in sources for file in files]
        return "target-source" if all(selected) else "mixed-macro" if any(selected) else "dependency"

    def signature(self, node, walls):
        identifier = node.get("id")
        if node.get("kind") != "FunctionDecl":
            if self.decl(identifier, "method_signature_api", walls) != "FunctionDecl return and parameter projection v1":
                walls.add("evidence:method-signature-api")
            result = self.decl(identifier, "method_result_type", walls)
            parameters = self.decl(identifier, "method_parameter_types", walls)
            variadic = self.decl(identifier, "method_variadic", walls)
            exception = self.decl(identifier, "method_exception_spec", walls)
            if type(exception) is not int or exception != 0:
                walls.add("signature:exception-specification")
        else:
            function = self.type_of(identifier, walls)
            if not isinstance(function, dict) or function.get("kind") != "function":
                walls.add("signature:unrepresented-function-type")
                function = {}
            result, parameters, variadic = function.get("result"), function.get("parameters"), function.get("variadic")
        if result is None:
            walls.add("signature:unrepresented-result")
        elif integral(result):
            if result.get("kind") != "builtin":
                walls.add("signature:qualified-result")
        elif result != {"kind": "builtin", "name": "void"}:
            walls.add("signature:nonintegral-result")
        if not isinstance(parameters, list):
            walls.add("signature:missing-parameters")
        else:
            if any(parameter is None for parameter in parameters):
                walls.add("signature:unrepresented-parameter")
            if any(parameter is not None and not integral(parameter, reference=True) for parameter in parameters):
                walls.add("signature:nonintegral-parameter")
        if variadic is not False:
            walls.add("signature:variadic-or-unestablished")

    def record(self, identifier, used, walls):
        if not handle(identifier):
            walls.add("record:missing-owner")
            return
        self.canonical(identifier, walls)
        self.scopes(identifier, walls, include_self=True)
        def field(key):
            return self.decl(identifier, key, walls)
        if field("record_shape_api") != "CXXRecordDecl aggregate member shape v1":
            walls.add("evidence:record-shape-api")
        for key, expected, reason in (("record_complete", True, "incomplete"),
            ("record_union", False, "union"), ("record_aggregate", True, "nonaggregate"),
            ("record_base_count", 0, "bases"), ("record_trivial_destructor", True, "nontrivial-destruction"),
            ("record_user_destructor", False, "user-destructor"), ("record_attribute_count", 0, "attributes")):
            value = field(key)
            if type(value) is not type(expected) or value != expected:
                walls.add("record:" + reason)
        complete = [node for _, node in self.raw.get(identifier, []) if node.get("completeDefinition") is True]
        if not complete:
            walls.add("record:absent-complete-source")
            return
        fields = [child for child in complete[0].get("inner", []) if child.get("kind") == "FieldDecl"]
        field_ids = [child.get("id") for child in fields]
        if any([child.get("id") for child in source.get("inner", []) if child.get("kind") == "FieldDecl"] != field_ids for source in complete[1:]):
            walls.add("record:conflicting-complete-source")
        count = field("record_field_count")
        if type(count) is not int or count != len(fields):
            walls.add("record:field-census-mismatch")
        attributes = [child.get("kind") for child in complete[0].get("inner", []) if str(child.get("kind")).endswith("Attr")]
        attribute_count = field("record_attribute_count")
        if type(attribute_count) is int and attribute_count == len(attributes):
            walls.discard("record:attributes")
            walls.update("record:attribute:" + kind for kind in attributes)
        else:
            walls.add("record:attribute-census-mismatch")
        for index, member in enumerate(fields):
            mid = member.get("id")
            if self.canonical(mid, walls) != mid:
                walls.add("record:field-identity")
            field_index = self.decl(mid, "field_index", walls)
            if type(field_index) is not int or field_index != index or self.decl(mid, "field_parent", walls) != identifier:
                walls.add("record:field-order-or-owner")
            if type(self.decl(mid, "field_mutable", walls)) is not bool:
                walls.add("evidence:field-mutable")
            field_walls = set()
            type_ = self.type_of(mid, field_walls)
            prefix = "record:used-field-" if mid in used else "record:unused-field-"
            walls.update(prefix + wall for wall in field_walls)
            if not integral(type_):
                walls.add("record:used-nonintegral-field" if mid in used else "record:unused-nonintegral-field")
            for key, reason in (("field_bitfield", "bitfield"), ("field_initializer", "initializer")):
                if self.decl(mid, key, walls) is not False:
                    walls.add("record:" + reason)
            field_attributes = self.decl(mid, "field_attribute_count", walls)
            if type(field_attributes) is not int or field_attributes != 0:
                walls.add("record:field-attributes")

    def member(self, node, owner, walls):
        target = node.get("referencedMemberDecl")
        kind = self.decl(target, "kind", walls)
        children = node.get("inner", [])
        base = children[0] if len(children) == 1 else {}
        if base.get("kind") != "CXXThisExpr":
            walls.add("member:non-this-base")
        else:
            base_type = self.type_of(base.get("id"), walls, expression=True)
            base_type = base_type if isinstance(base_type, dict) else {}
            pointee = unqualified(base_type.get("pointee"))
            if base_type.get("kind") != "pointer" or pointee.get("kind") != "record" or self.canonical(pointee.get("declaration"), walls) != self.canonical(owner, walls):
                walls.add("member:receiver-type-mismatch")
        if type(node.get("isArrow")) is not bool:
            walls.add("member:missing-arrow-evidence")
        if kind == "FieldDecl":
            if self.decl(target, "field_parent", walls) != owner:
                walls.add("member:other-owner-or-base-class")
            if not integral(self.type_of(target, walls)):
                walls.add("member:nonintegral-field")
            if self.decl(target, "field_bitfield", walls) is not False:
                walls.add("member:bitfield")
            if not integral(self.type_of(node.get("id"), walls, expression=True)):
                walls.add("member:nonintegral-expression")
        elif kind not in FUNCTIONS:
            walls.add("member:nonfield-target")
        mutable = self.decl(target, "field_mutable", walls) if kind == "FieldDecl" else None
        if kind == "FieldDecl" and type(mutable) is not bool:
            walls.add("evidence:field-mutable")
        return {"occurrence": node.get("id"), "target": target, "target_kind": kind,
                "base_kind": base.get("kind"), "is_arrow": node.get("isArrow"), "mutable": mutable}

    def call(self, node, walls):
        children = node.get("inner", [])
        callee = children[0] if children else {}
        while callee.get("kind") in TRANSPARENT and len(callee.get("inner", [])) == 1:
            callee = callee["inner"][0]
        reference = callee.get("referencedDecl", {})
        target = callee.get("referencedMemberDecl") if callee.get("kind") == "MemberExpr" else reference.get("id") if isinstance(reference, dict) else None
        if not handle(target) or self.decl(target, "kind", walls) not in FUNCTIONS:
            walls.add("call:unresolved-or-indirect")
            return {"occurrence": node.get("id"), "target": target, "body_ordinals": []}
        canonical = self.canonical(target, walls)
        target_sources = [raw for _, raw in self.raw.get(target, []) if raw.get("kind") in FUNCTIONS]
        if target_sources:
            self.signature(target_sources[0], walls)
        else:
            walls.add("evidence:call-target-source-absent")
        if self.decl(target, "kind", walls) != "FunctionDecl" and self.decl(target, "method_virtual", walls) is not False:
            walls.add("call:virtual-or-unestablished-target")
        bodies = self.by_canonical.get(canonical, [])
        walls.add("call:direct")
        if not bodies:
            walls.add("call:external-body")
        if any(effectful(argument) for argument in children[1:]):
            walls.add("call:argument-effects")
        return {"occurrence": node.get("id"), "target": target, "canonical": canonical,
                "body_ordinals": list(bodies)}

    def body(self, ordinal, path, node, body, sources, capture_dir):
        walls, members, calls, used = set(), [], [], set()
        identifier = node.get("id")
        kind = node.get("kind")
        self.canonical(identifier, walls)
        self.scopes(identifier, walls)
        if not identifier_name(node.get("name")):
            walls.add("declaration:unsupported-name")
        if kind not in {"FunctionDecl", "CXXMethodDecl"}:
            walls.add("declaration:" + kind)
        implicit = self.decl(identifier, "implicit", walls)
        if type(implicit) is not bool:
            walls.add("evidence:implicit-flag")
        if implicit is not False:
            walls.add("declaration:implicit")
        if self.decl(identifier, "dependent_context", walls) is not False:
            walls.add("declaration:dependent-context")
        if self.decl(identifier, "owning_module", walls) is not None:
            walls.add("declaration:module")
        for key in ("function_templated_kind", "template_specialization_kind", "function_attribute_count"):
            value = self.decl(identifier, key, walls)
            if type(value) is not int or value != 0:
                walls.add("declaration:" + key)
        for key in ("function_has_skipped_body", "function_will_have_body", "function_has_defining_attr",
                    "function_late_template_parsed", "function_explicitly_defaulted", "deleted_as_written"):
            if self.decl(identifier, key, walls) is not False:
                walls.add("declaration:" + key)
        owner = self.decl(identifier, "semantic_context", walls)
        static = self.decl(identifier, "method_static", walls) if kind == "CXXMethodDecl" else None
        instance = kind == "CXXMethodDecl" and static is False
        if kind == "CXXMethodDecl" and type(static) is not bool:
            walls.add("receiver:unestablished-static")
        method_flags = {}
        if kind == "CXXMethodDecl":
            if self.decl(identifier, "method_shape_api", walls) != "CXXMethodDecl receiver shape v1":
                walls.add("evidence:method-shape-api")
            if self.decl(identifier, "method_parent", walls) != owner:
                walls.add("receiver:owner-mismatch")
            for key in ("method_const", "method_volatile", "method_virtual", "method_pure"):
                value = self.decl(identifier, key, walls)
                method_flags[key] = value
                if type(value) is not bool:
                    walls.add("evidence:" + key)
                if key != "method_const" and value is not False:
                    walls.add("receiver:" + key.removeprefix("method_"))
            qualifier = self.decl(identifier, "method_ref_qualifier", walls)
            method_flags["method_ref_qualifier"] = qualifier
            if type(qualifier) is not int or qualifier != 0:
                walls.add("receiver:ref-qualified-or-unestablished")
        self.signature(node, walls)
        if instance:
            walls.add("receiver:instance")
        allowed_references = {child.get("id") for _, child in inner_walk(node)
                              if child.get("kind") in {"ParmVarDecl", "VarDecl"}}
        kinds = collections.Counter()
        body_nodes = list(inner_walk(body))
        parents = dict(body_nodes)
        for relative, child in body_nodes:
            child_kind = child.get("kind")
            if child_kind is None and child == {}:
                continue  # empty for-header slots; not statements
            kinds[str(child_kind)] += 1
            if child_kind == "MemberExpr":
                walls.add("node:MemberExpr")
                members.append(self.member(child, owner, walls))
                if members[-1]["target_kind"] == "FieldDecl":
                    used.add(members[-1]["target"])
            elif child_kind in CALLS:
                calls.append(self.call(child, walls))
            elif child_kind not in BASE_KINDS:
                walls.add("node:" + str(child_kind))
            if child_kind == "CXXThisExpr" and (not relative or parents[relative[:-1]].get("kind") != "MemberExpr"):
                walls.add("receiver:escaped-this")
            if child_kind in {"BinaryOperator", "CompoundAssignOperator", "UnaryOperator"}:
                for operand in [child, *child.get("inner", [])]:
                    if not integral(self.type_of(operand.get("id"), walls, expression=True)):
                        walls.add("expression:nonintegral-operator-type")
            if child_kind in {"BinaryOperator", "CompoundAssignOperator"}:
                opcode = child.get("opcode")
                if opcode not in BINARY and not (child_kind == "CompoundAssignOperator" and opcode in {op + "=" for op in BINARY - {"=", ",", "&&", "||", "==", "!=", "<=", ">="}}):
                    walls.add("operator:" + str(opcode))
                if child_kind == "BinaryOperator" and opcode not in {"&&", "||", ",", "="} and any(effectful(operand) for operand in child.get("inner", [])):
                    walls.add("expression:unsequenced-operand-effects")
            if child_kind == "UnaryOperator" and child.get("opcode") not in UNARY:
                walls.add("operator:" + str(child.get("opcode")))
            if child_kind == "ImplicitCastExpr" and child.get("castKind") not in CASTS:
                walls.add("cast:" + str(child.get("castKind")))
            if child_kind == "VarDecl":
                local_type = self.type_of(child.get("id"), walls)
                if not integral(local_type, reference=True):
                    walls.add("local:nonintegral-type")
                for key, expected in (("storage_duration", "automatic"), ("tls", "none"),
                                      ("attribute_count", 0), ("local", True), ("local_or_parameter", True)):
                    value = self.get(self.variables, child.get("id"), key, walls, "variable")
                    if type(value) is not type(expected) or value != expected:
                        walls.add("local:" + key)
                storage = self.get(self.variables, child.get("id"), "storage_class", walls, "variable")
                if storage not in {"none", "auto", "register"}:
                    walls.add("local:storage_class")
                constexpr = self.get(self.variables, child.get("id"), "constexpr", walls, "variable")
                if type(constexpr) is not bool or (constexpr and not
                    (isinstance(local_type, dict) and local_type.get("kind") == "qualified"
                     and local_type.get("const") is True and integral(local_type))):
                    walls.add("local:constexpr")
            if child_kind == "DeclRefExpr":
                reference = child.get("referencedDecl", {})
                if not isinstance(reference, dict):
                    raise ValueError("referencedDecl must be an object")
                target = reference.get("id")
                target_kind = self.decl(target, "kind", walls)
                if target not in allowed_references and target_kind not in FUNCTIONS:
                    walls.add("reference:nonlocal-declaration")
        if instance:
            self.record(owner, used, walls)
        return {"ordinal": ordinal, "path": list(path), "occurrence": identifier,
            "kind": kind, "implicit": implicit, "instance": instance,
            "ownership": self.ownership(identifier, sources, capture_dir),
            "receiver": owner if instance else None, "receiver_flags": method_flags,
            "method_static_established": type(static) is bool if kind == "CXXMethodDecl" else None,
            "body_kinds": dict(sorted(kinds.items())), "members": members, "calls": calls,
            "direct_walls": sorted(walls)}


def price_probe(document, sources, capture_dir):
    probe = Probe(document)
    sources = {pathlib.Path(source).resolve(strict=True) for source in sources}
    if not sources or any(not source.is_file() for source in sources):
        raise ValueError("select at least one existing source file")
    capture_dir = pathlib.Path(capture_dir).resolve(strict=True)
    if not capture_dir.is_dir():
        raise ValueError("capture directory is not a directory")
    rows = [probe.body(i, path, node, body, sources, capture_dir)
            for i, (path, node, body) in enumerate(probe.functions)]
    graph = [{index for call in row["calls"] for index in call["body_ordinals"]} for row in rows]
    closures = []
    for row in rows:
        reached, pending = set(), list(graph[row["ordinal"]])
        while pending:
            index = pending.pop()
            if index not in reached:
                reached.add(index)
                pending.extend(graph[index])
        closures.append(reached)
    recursive = {index for index, reached in enumerate(closures) if index in reached}
    for row, reached in zip(rows, closures):
        walls = set(row["direct_walls"])
        for index in reached:
            walls.update(rows[index]["direct_walls"])
        if reached & recursive:
            walls.add("call:recursive")
        row["in_recursive_component"] = row["ordinal"] in recursive
        row["reaches_recursion"] = bool(reached & recursive)
        row["reachable_body_ordinals"] = sorted(reached)
        row["closure_walls"] = sorted(walls)
    selected = [row for row in rows if row["ownership"] == "target-source" and row["implicit"] is False]
    methods = [row for row in selected if row["instance"]]
    scenarios = {}
    for name, removed in (("current", frozenset()), ("aggregate-this-and-members", RECEIVER),
                           ("existing-receiver-integral-projection", SNAPSHOT),
                           ("existing-receiver-projection-and-visibility", SNAPSHOT | {"record:attribute:VisibilityAttr"}),
                           ("existing-receiver-projection-visibility-and-direct-calls", SNAPSHOT | DIRECT_CALL | {"record:attribute:VisibilityAttr"})):
        def remaining(walls):
            return {wall for wall in walls if wall not in removed and not
                    (name.startswith("existing-receiver") and wall.startswith("record:unused-field-"))}
        scenarios[name] = {"hypothetically_removed_walls": sorted(removed),
            "hypothetically_removed_prefixes": ["record:unused-field-"] if name.startswith("existing-receiver") else [],
            "direct": rank(remaining(row["direct_walls"]) for row in methods),
            "closure": rank(remaining(row["closure_walls"]) for row in methods)}
    return {"format": FORMAT, "status": "COMPLETE", "scope": "observed-wall-pricing-only",
        "profile": PROFILE, "semantic_admission_claimed": False, "execution": "not-attempted",
        "semantic_probe_validation": "not-performed; correlate input hash with Lean runtime census",
        "unpriced_semantic_checks": ["source/metadata ancestry and redeclaration coherence",
            "expression typing/promotion and AST arity/context validation",
            "local binding order, initialization and alias/lifetime effects",
            "call argument binding, sequencing and dynamic dispatch",
            "constructor initializer lists and implicit construction/destruction",
            "defined behavior, resource bounds and termination"],
        "counting_basis": "retained root/inner body occurrences; no deduplication",
        "ownership_basis": "physical declared-name expansion and spelling; both selected",
        "body_occurrences": len(rows), "ownership_counts": dict(sorted(collections.Counter(row["ownership"] for row in rows).items())),
        "target_explicit_bodies": len(selected), "target_explicit_instance_methods": len(methods),
        "target_unestablished_method_static": sum(row["kind"] == "CXXMethodDecl" and not row["method_static_established"] for row in selected),
        "unestablished_implicit_flags": sum(type(row["implicit"]) is not bool for row in rows),
        "method_const_counts": dict(sorted(collections.Counter(str(row["receiver_flags"].get("method_const")) for row in methods).items())),
        "scenarios": scenarios, "bodies": rows}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=pathlib.Path)
    parser.add_argument("--sources", nargs="+", required=True, type=pathlib.Path)
    parser.add_argument("--capture-dir", type=pathlib.Path, default=pathlib.Path.cwd())
    parser.add_argument("--out", required=True, type=pathlib.Path)
    parser.add_argument("--max-input-mib", type=int, default=128)
    args = parser.parse_args(argv)
    if args.max_input_mib <= 0:
        parser.error("input byte bound must be positive")
    try:
        verify_baseline()
        tool_hash = hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()
        refuse_output_alias(args.out, [args.input, *args.sources])
        before = args.input.stat()
        if before.st_size > args.max_input_mib * 1024 * 1024:
            raise ValueError("input exceeds explicit byte bound")
        contents = args.input.read_bytes()
        after = args.input.stat()
        if (before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns) != (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns) or len(contents) != before.st_size:
            raise ValueError("input changed during read")
        document = json.loads(contents.decode("utf-8"), object_pairs_hook=unique_object,
                              parse_float=refuse_numeric_token, parse_constant=refuse_numeric_token)
        # Reject lone surrogates even in opaque supplement values.
        pending = [document]
        while pending:
            value = pending.pop()
            if isinstance(value, dict):
                pending.extend(value.keys()); pending.extend(value.values())
            elif isinstance(value, list):
                pending.extend(value)
            elif isinstance(value, str):
                value.encode("utf-8")
        report = price_probe(document, args.sources, args.capture_dir)
        verify_baseline()
        if hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest() != tool_hash:
            raise ValueError("pricing tool changed during run")
        report.update(input_bytes=len(contents), input_sha256=hashlib.sha256(contents).hexdigest(),
                      tool_sha256=tool_hash, baseline_model_sha256=BASELINE_MODEL_SHA256)
        publish_report(args.out, report)
    except (OSError, ValueError, TypeError, RecursionError) as error:
        print("method closure pricing refused: " + str(error), file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
