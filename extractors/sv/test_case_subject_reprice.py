"""Shape checks for CaseStatement:subject repricing."""
import unittest

from case_subject_reprice import case_subject_features


class CaseSubjectReprice(unittest.TestCase):
    def test_time_and_constant_subjects(self):
        self.assertEqual(
            case_subject_features("module m; initial case ($time) 1: ; endcase endmodule",
                                  "case ($time) 1: ; endcase"),
            ("time-subject",))
        self.assertEqual(
            case_subject_features("module m; localparam int VALUE=3; initial "
                                  "case (VALUE + 2) 5: ; endcase endmodule",
                                  "case (VALUE + 2) 5: ; endcase"),
            ("constant-expression-subject",))

    def test_packed_aggregate_subjects(self):
        self.assertEqual(
            case_subject_features(
                "typedef union packed { logic [1:0] state; logic [1:0] raw; } U; "
                "U regs; initial case (regs.state) 0: ; endcase",
                "case (regs.state) 0: ; endcase"),
            ("packed-union-member-subject",))
        self.assertEqual(
            case_subject_features(
                "typedef struct packed { logic [1:0] mode; } S; S packed_state; "
                "initial case (packed_state.mode[1:0]) 0: ; endcase",
                "case (packed_state.mode[1:0]) 0: ; endcase"),
            ("packed-struct-part-select-subject",))

    def test_unknown_subject_stays_loud(self):
        self.assertEqual(
            case_subject_features("module m; initial case (f()) 0: ; endcase endmodule",
                                  "case (f()) 0: ; endcase"),
            ("unsupported-subject-expression",))


if __name__ == "__main__":
    unittest.main()
