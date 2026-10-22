import unittest
from elab_task_reprice import elab_task_features
class ElabTaskReprice(unittest.TestCase):
    def test_info(self): self.assertEqual(elab_task_features('$info("x");'), ("info",))
    def test_warning(self): self.assertEqual(elab_task_features('$warning("x");'), ("warning",))
    def test_both(self): self.assertEqual(elab_task_features('$warning("x"); $info("y");'), ("info", "warning"))
if __name__ == "__main__": unittest.main()
