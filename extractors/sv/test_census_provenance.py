import unittest

import census


class PublicCensusProvenance(unittest.TestCase):
    def test_public_payload_uses_portable_corpus_location(self):
        provenance = {"corpus_name": "sample", "corpus_path": "/unpublished/location/tests",
                      "corpus_files": 3}
        summary = {"corpus": "/unpublished/location/tests", "by_status": {"clean": 3},
                   "elapsed_seconds": 7.5}
        payload = census.committed_payload(provenance, summary)
        self.assertEqual(payload["provenance"]["corpus_path"], "<corpus>/tests")
        self.assertEqual(payload["summary"]["corpus"], "<corpus>")
        self.assertEqual(payload["summary"]["by_status"], {"clean": 3})
        self.assertNotIn("elapsed_seconds", payload["summary"])

    def test_local_measurement_is_not_mutated(self):
        provenance = {"corpus_path": "/unpublished/location/tests"}
        summary = {"corpus": "/unpublished/location/tests"}
        census.committed_payload(provenance, summary)
        self.assertEqual(provenance["corpus_path"], "/unpublished/location/tests")
        self.assertEqual(summary["corpus"], "/unpublished/location/tests")

    def test_public_rendering_is_idempotent(self):
        payload = census.committed_payload({"corpus_path": "/unpublished/location/tests"},
                                           {"total_files": 3})
        self.assertEqual(census.committed_payload(payload["provenance"], payload["summary"]),
                         payload)

    def test_absent_explicit_path_remains_absent(self):
        payload = census.committed_payload({}, {"corpus": None})
        self.assertNotIn("corpus_path", payload["provenance"])
        self.assertIsNone(payload["summary"]["corpus"])

    def test_null_provenance_path_remains_null(self):
        payload = census.committed_payload({"corpus_path": None}, {"corpus": None})
        self.assertIsNone(payload["provenance"]["corpus_path"])
        self.assertIsNone(payload["summary"]["corpus"])


if __name__ == "__main__":
    unittest.main()
