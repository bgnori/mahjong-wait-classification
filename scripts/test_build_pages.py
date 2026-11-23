import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import build_pages


class BuildPagesTest(unittest.TestCase):
    def test_build_includes_metrics_page_and_empty_data(self) -> None:
        with tempfile.TemporaryDirectory() as temporary_directory:
            output = Path(temporary_directory)
            with patch.object(build_pages, "result_revision", return_value={}):
                build_pages.build(output, "example/project")
            self.assertTrue((output / "build-metrics/index.html").is_file())
            self.assertEqual(json.loads((output / "build-metrics/data.json").read_text()), [])

    def test_write_report_adds_result_revision(self) -> None:
        revision = {
            "commit": "a" * 40,
            "committedAt": "2026-10-27T12:00:00+00:00",
            "sourcePath": "reports/example.json",
            "commitUrl": "https://github.com/example/project/commit/" + "a" * 40,
        }
        with tempfile.TemporaryDirectory() as temporary_directory:
            directory = Path(temporary_directory)
            source = directory / "source.json"
            destination = directory / "destination.json"
            source.write_text(
                json.dumps(
                    {
                        "reportType": "mahjong-wait-report",
                        "schemaVersion": 2,
                        "tileCount": 4,
                    }
                ),
                encoding="utf-8",
            )

            build_pages.write_report(source, destination, revision)

            result = json.loads(destination.read_text(encoding="utf-8"))
            self.assertEqual(result["tileCount"], 4)
            self.assertEqual(result["resultRevision"], revision)


if __name__ == "__main__":
    unittest.main()
