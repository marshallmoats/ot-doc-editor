#!/usr/bin/env python3
"""Check the configurable collaboration delay setting."""
import os
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from web.server import configured_collaboration_delay


class CollaborationDelayTests(unittest.TestCase):
    def test_disabled_by_default(self):
        with patch.dict(os.environ, {}, clear=True):
            self.assertEqual(configured_collaboration_delay(), 0)

    def test_reads_milliseconds(self):
        with patch.dict(os.environ, {"OT_COLLAB_DELAY_MS": "250"}):
            self.assertEqual(configured_collaboration_delay(), 250)

    def test_rejects_invalid_or_excessive_values(self):
        for value in ("fast", "-1", "60001"):
            with self.subTest(value=value), patch.dict(
                os.environ, {"OT_COLLAB_DELAY_MS": value}
            ):
                with self.assertRaises(SystemExit):
                    configured_collaboration_delay()


if __name__ == "__main__":
    unittest.main()
