"""Diagnostic-free qualified-if lowering for the legacy self-check tier."""
import unittest

from test_bit_queries import lower, nodes


def source(qualifier, conditions, fallback="result = 99;"):
    chain = ""
    for index, condition in enumerate(conditions):
        keyword = qualifier if index == 0 else "else if"
        chain += f"{keyword} ({condition}) result = {index + 1}; "
    return (
        "module top; initial begin int value, result; value = 5; "
        f"{chain}else {fallback} if (result === 99) $display(\"PASS\"); "
        "else $display(\"FAIL\"); end endmodule"
    )


class QualifiedIf(unittest.TestCase):
    def test_unique_disjoint_literal_chain_with_fallback(self):
        design = lower(source("unique if", ["value == 1", "value == 2"]))
        self.assertFalse(any(n.get("kind") == "Unsupported" for n in nodes(design)))
        self.assertEqual(
            [n.get("qualified_fallback_lowered") for n in nodes(design)
             if n.get("qualified_fallback_lowered")],
            ["Unique"],
        )

    def test_priority_chain_with_fallback(self):
        design = lower(source("priority if", ["value > 1", "value > 0"]))
        self.assertFalse(any(n.get("kind") == "Unsupported" for n in nodes(design)))
        self.assertEqual(
            [n.get("qualified_fallback_lowered") for n in nodes(design)
             if n.get("qualified_fallback_lowered")],
            ["Priority"],
        )

    def test_ambiguous_unique_chain_stays_loud(self):
        design = lower(source("unique if", ["value > 1", "value > 0"]))
        self.assertIn(
            "ConditionalStatement:Unique",
            [n.get("sv_kind") for n in nodes(design)],
        )

    def test_missing_fallback_stays_loud(self):
        design = lower(
            "module top; initial begin int value, result; value = 5; "
            "unique if (value == 1) result = 1; "
            "else if (value == 2) result = 2; end endmodule"
        )
        self.assertIn(
            "ConditionalStatement:Unique",
            [n.get("sv_kind") for n in nodes(design)],
        )


if __name__ == "__main__":
    unittest.main()
