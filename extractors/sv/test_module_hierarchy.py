"""Concrete per-instance binding, IEEE 1800-2023 clauses 6/23/27."""
from pathlib import Path
import unittest

import extract
from test_bit_queries import lower, nodes
from test_division import symbolic
from test_elaborated_generate import declarations, walls

# REFERENCE: b05b086e84da0718bb4efd59 24.03-s004 2026-10-20 | tests=ModuleHierarchy-isolation | source=Examples/system-verilog/module_hierarchy/isolation.sv@sha256:58f1de79feab7c676401bdd7ca41bf17c57efd0f772733286ba4fb545ea15f02 | top=top | args=["-ii_val"] | map=Examples/system-verilog/module_hierarchy/README.md#static-module-hierarchy
# REFERENCE: 2baf3fa00845f0d6726cf5e2 24.03-s004 2026-10-20 | tests=ModuleHierarchy-nested | source=Examples/system-verilog/module_hierarchy/nested.sv@sha256:7599f454d9166acc336c927061835a147224c6799967485caabff896ae5f310d | top=top | args=["-ii_val"] | map=Examples/system-verilog/module_hierarchy/README.md#static-module-hierarchy
# REFERENCE: 75385d02e64d838f328846a4 24.03-s004 2026-10-20 | tests=ModuleHierarchy-arrays | source=Examples/system-verilog/module_hierarchy/arrays.sv@sha256:2f4664d266dc515662fb9a843cfcef3d837e8c4cd3b4d2b3b07f7b3cbf0cca65 | top=top | args=["-ii_val"] | map=Examples/system-verilog/module_hierarchy/README.md#static-module-hierarchy
# REFERENCE: 6056c5d8241d48f9d912f18d 24.03-s004 2026-10-20 | tests=ModuleHierarchy-locals_timing | source=Examples/system-verilog/module_hierarchy/locals_timing.sv@sha256:88f8dd387784b7a6504f5aa8c5774bd6898ec17ed1aacb57b25b2b95810990c5 | top=top | args=["-ii_val"] | map=Examples/system-verilog/module_hierarchy/README.md#static-module-hierarchy
# REFERENCE: dc2f06ab607035ca9459bb25 24.03-s004 2026-10-20 | tests=ModuleHierarchy-shared_package | source=Examples/system-verilog/module_hierarchy/shared_package.sv@sha256:fbefc7ee9d232cdc73f2114f0b5ba00a4d016adc92e110126f92bc5fdf7605e8 | top=top | args=["-ii_val"] | map=Examples/system-verilog/module_hierarchy/README.md#static-module-hierarchy
# REFERENCE: c26913132f0e3cb1ae8a4313 24.03-s004 2026-10-20 | tests=ModuleHierarchy-parameters | source=Examples/system-verilog/module_hierarchy/parameters.sv@sha256:ca6bfad08382fdfd73fda6e712c4296155ea59268b7c7ed7e95fa4861a1b0350 | top=top | args=["-ii_val"] | map=Examples/system-verilog/module_hierarchy/README.md#static-module-hierarchy
# REFERENCE: f554919f814b768c951ce265 24.03-s004 2026-10-20 | tests=ModuleHierarchy-ports | source=Examples/system-verilog/module_hierarchy/ports.sv@sha256:2a3714921a7c2714392c5402a6c299262e6f2a16bed19a99cfe0762187745dad | top=top | args=["-ii_val"] | map=Examples/system-verilog/module_hierarchy/README.md#static-module-hierarchy
# REFERENCE: c5c847a2dc72bfe3d1b5cc96 24.03-s004 2026-10-20 | tests=ModuleHierarchy-program_kind | source=Examples/system-verilog/module_hierarchy/program_kind.sv@sha256:d1d3d64558ecc4dafe7734dcb2e0e5a0e0c307fbd59a441286dab7766d70eaa4 | top=top | args=["-ii_val"] | map=Examples/system-verilog/module_hierarchy/README.md#static-module-hierarchy
# REFERENCE: ee8714f2a4cf6e37caa01906 24.03-s004 2026-10-20 | tests=ModuleHierarchy-initializer | source=Examples/system-verilog/module_hierarchy/initializer.sv@sha256:b2c565aa68bb9c8609deb4055fd892f7933f0b479f6318b0ee3a6ba0e7d69b9c | top=top | args=["-ii_val"] | map=Examples/system-verilog/module_hierarchy/README.md#static-module-hierarchy
# REFERENCE: 0963959003dff2b501ae4b57 24.03-s004 2026-10-20 | tests=ModuleHierarchy-timescale | source=Examples/system-verilog/module_hierarchy/timescale.sv@sha256:23ee1928880921ed2b076a5571c852053a347937ae4d1ec9de3e0a78678c8bb3 | top=top | args=["-ii_val"] | map=Examples/system-verilog/module_hierarchy/README.md#static-module-hierarchy
# REFERENCE: 9f39189729f25f270a2890d3 24.03-s004 2026-10-20 | tests=ModuleHierarchy-storage | source=Examples/system-verilog/module_hierarchy/storage.sv@sha256:8cb77f64a1b76e6d308f8a65da3358ab2764afc20bbc7a4873ac8641aa0c78e7 | top=top | args=["-ii_val"] | map=Examples/system-verilog/module_hierarchy/README.md#static-module-hierarchy
# SYNTHETIC-ORACLE: tests=ModuleHierarchy-binding-and-admission | origin=spec | authority=docs/sv-module-hierarchy.md | map=identity:actual-instance-declarations;references:bound-symbols;scope:injective-routes;packages:one-original-slot;invalid:frontend-barrier;ports:unmodelled-propagation;timescale:no-rescaling;limits:1024-instances-64-depth;symbolic:unchanged


def fixture(name):
    return lower(Path('Examples/system-verilog/module_hierarchy', name+'.sv').read_text())


class ModuleHierarchy(unittest.TestCase):
    def test_repeated_instances_use_distinct_declaration_storage(self):
        d = fixture('isolation')
        self.assertFalse(walls(d))
        names = [n['name'] for n in declarations(d)]
        self.assertEqual(len(names), 2)
        self.assertEqual(len(set(names)), 2)
        self.assertTrue(all(name.startswith('$hierarchy:') for name in names))
        self.assertTrue(d['modules'][0]['hierarchy_lowered'])

    def test_parent_reference_before_instance_declaration_is_prebound(self):
        d = lower('module child;int x;endmodule module top;'
                  'initial u.x=1;child u();endmodule')
        self.assertFalse(walls(d))
        target, = [n['target']['name'] for n in nodes(d) if n.get('kind')=='BlockingAssign']
        self.assertEqual(target, declarations(d)[0]['name'])

    def test_nested_generate_and_upward_references_are_bound(self):
        d = fixture('nested')
        self.assertFalse(walls(d))
        names = {n['name'] for n in declarations(d)}
        self.assertEqual(len(names), 3)
        self.assertTrue(all(n['name'] in names for n in nodes(d) if n.get('kind')=='Ident'))

    def test_per_instance_parameter_types_and_query_widths(self):
        d = fixture('parameters')
        self.assertFalse(walls(d))
        self.assertEqual([n['width'] for n in declarations(d)], [4, 8, 12])

    def test_negative_and_descending_instance_array_bindings(self):
        d = fixture('arrays')
        self.assertFalse(walls(d))
        names = [n['name'] for n in declarations(d)]
        self.assertEqual(len(names), 8)
        self.assertEqual(len(set(names)), 8)
        self.assertTrue(all(n['name'] in names for n in nodes(d) if n.get('kind')=='Ident'))

    def test_recursive_array_walker_keeps_each_frontend_element_distinct(self):
        d = lower('module child;int x;endmodule module top;child u[1:0][0:1]();endmodule')
        self.assertFalse(walls(d))
        self.assertEqual(len({n['name'] for n in declarations(d)}), 4)

    def test_procedural_locals_are_per_actual_instance(self):
        d = fixture('locals_timing')
        self.assertFalse(walls(d))
        locals_ = [n['name'] for n in nodes(d) if n.get('kind')=='LocalDecl']
        self.assertEqual(len(locals_), 3)
        self.assertEqual(len(set(locals_)), 3)

    def test_package_storage_is_not_copied_per_instance(self):
        d = fixture('shared_package')
        self.assertFalse(walls(d))
        self.assertEqual(len(declarations(d)), 1)
        self.assertEqual(len({n['name'] for n in nodes(d) if n.get('kind')=='Ident'}), 1)

    def test_fixed_array_cells_and_packed_members_keep_instance_binding(self):
        d = fixture('storage')
        self.assertFalse(walls(d))
        names = [n['name'] for n in declarations(d)]
        names += [n['name'] for n in nodes(d) if n.get('kind')=='LocalDecl']
        self.assertEqual(len(names), len(set(names)))
        self.assertTrue(all(n['name'] in names for n in nodes(d) if n.get('kind')=='Ident'))

    def test_inactive_instances_contribute_no_storage_or_process(self):
        d = lower('module child;string unsupported_value;endmodule module top;'
                  'if(0)begin:g child u();end endmodule')
        self.assertFalse(walls(d))
        self.assertFalse(declarations(d))

    def test_active_child_members_are_not_ignored(self):
        d = lower('module child;function int f();return 1;endfunction endmodule '
                  'module top;child u();endmodule')
        self.assertIn('SubroutineSymbol:Subroutine', walls(d))

    def test_child_ports_refuse_even_when_unconnected(self):
        self.assertIn('Hierarchy:ports', walls(fixture('ports')))
        d = lower('module child(input logic x);endmodule module top;child u();endmodule')
        self.assertIn('Hierarchy:ports', walls(d))

    def test_program_and_interface_instances_are_not_module_processes(self):
        self.assertIn('Hierarchy:module-kind', walls(fixture('program_kind')))
        d = lower('interface child;endinterface module top;child u();endmodule')
        self.assertIn('Hierarchy:module-kind', walls(d))

    def test_distinct_time_units_do_not_silently_share_ticks(self):
        self.assertIn('Hierarchy:timescale', walls(fixture('timescale')))
        d = lower('module child;timeunit 1ns;timeprecision 1ps;endmodule '
                  'module top;timeunit 1ns;timeprecision 1ps;child u();endmodule')
        self.assertFalse(walls(d))

    def test_new_static_initializer_order_dependence_refuses(self):
        self.assertIn('Generate:initializer-order', walls(fixture('initializer')))
        d = lower('module child;int x=1;endmodule module top;child u();int x=u.x;endmodule')
        self.assertIn('Generate:initializer-order', walls(d))

    def test_empty_child_still_preserves_whole_design_validity_barrier(self):
        d = lower('module child;endmodule module top;child u();int x;int x;endmodule', require_valid=False)
        self.assertIn('Hierarchy:invalid-compilation', walls(d))

    def test_generated_names_cannot_capture_escaped_source_bindings(self):
        prefix = 'module child;int x;endmodule module top;child u();'
        name = declarations(lower(prefix+'endmodule'))[0]['name']
        d = lower(prefix+'int \\'+name+' ; endmodule')
        self.assertIn('Hierarchy:storage-collision', walls(d))

    def test_instance_expansion_is_bounded_without_partial_success(self):
        d = lower('module child;endmodule module top;child u[0:1024]();endmodule')
        self.assertIn('Hierarchy:instance-limit', walls(d))

    def test_depth_is_bounded(self):
        source = 'module leaf;endmodule '
        previous = 'leaf'
        for i in range(66):
            name = 'layer'+str(i)
            source += 'module '+name+';'+previous+' u();endmodule '
            previous = name
        self.assertIn('Hierarchy:instance-limit', walls(lower(source)))

    def test_top_ports_remain_top_ports(self):
        d = lower('module child;int x;endmodule module top(input logic a);child u();endmodule')
        self.assertFalse(walls(d))
        self.assertEqual([p['name'] for p in d['modules'][0]['ports']], ['a'])

    def test_symbolic_instance_vocabulary_is_unchanged(self):
        d = symbolic('module child;endmodule module divider #(parameter int N=8);child u();endmodule')
        self.assertIn('InstanceSymbol:Instance', walls(d))
        self.assertFalse(any(n.get('hierarchy_lowered') for n in nodes(d)))


if __name__ == '__main__':
    unittest.main()
