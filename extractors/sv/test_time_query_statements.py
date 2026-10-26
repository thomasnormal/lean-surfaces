"""Discarded zero-argument integer time queries are inert at time zero."""

import unittest

from pyslang.ast import Compilation
from pyslang.syntax import SyntaxTree

import extract


def extract_source(source):
    tree = SyntaxTree.fromText(source)
    compilation = Compilation()
    compilation.addSyntaxTree(tree)
    compilation.getAllDiagnostics()
    extract._SOURCE_BYTES = source.encode()
    return extract.convert_design(tree.sourceManager, compilation)


def nodes(value):
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from nodes(child)
    elif isinstance(value, list):
        for child in value:
            yield from nodes(child)


class TimeQueryStatements(unittest.TestCase):
    def test_zero_argument_queries_are_inert(self):
        design = extract_source(
            "module top; initial begin $time; $stime; end endmodule")
        marks = [node.get("time_query_statement") for node in nodes(design)
                 if node.get("time_query_statement")]
        self.assertEqual(marks, ["$time", "$stime"])
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_discarded_realtime_is_inert(self):
        design = extract_source(
            "module top; initial begin $realtime; end endmodule")
        marks = [node.get("realtime_query_statement") for node in nodes(design)
                 if node.get("realtime_query_statement")]
        self.assertEqual(marks, ["$realtime"])
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_argumented_queries_stay_loud(self):
        design = extract_source(
            "module top; int unit; initial begin $time(unit); $stime(unit); "
            "end endmodule")
        self.assertFalse(any(node.get("time_query_statement")
                             for node in nodes(design)))
        self.assertTrue(any(node.get("sv_kind") == "InvalidStatement"
                            for node in nodes(design)))

    def test_discarded_time_scale_queries_are_inert(self):
        design = extract_source(
            "`timescale 1ns/1ps\nmodule top; initial begin "
            "$timeunit; $timeprecision; end endmodule")
        marks = [node.get("time_scale_statement") for node in nodes(design)
                 if node.get("time_scale_statement")]
        self.assertEqual(marks, ["$timeunit", "$timeprecision"])
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
