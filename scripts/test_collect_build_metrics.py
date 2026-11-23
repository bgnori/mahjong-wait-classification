import io
import json
import unittest
import urllib.parse
import urllib.request
import zipfile
from unittest.mock import patch

import collect_build_metrics as metrics


class CollectBuildMetricsTest(unittest.TestCase):
    def setUp(self):
        self.repository = metrics.REPOSITORIES[0]
        self.artifact = {
            "id": 123, "expired": False,
            "workflow_run": {"id": 42, "head_branch": "main", "head_sha": "a" * 40},
        }
        self.record = {
            "schemaVersion": 1, "repository": self.repository, "commit": "a" * 40,
            "coreCommit": "b" * 40, "runId": "42", "exitCode": 0,
            "startedAt": "2026-11-23T00:00:00+00:00", "leanToolchain": "lean4",
            "elapsedSeconds": 10.0, "peakTreePssMiB": 900.0,
            "modulePeakPssMiB": {"MahjongDomain/Hand.lean": None},
        }

    def archive(self, record):
        buffer = io.BytesIO()
        with zipfile.ZipFile(buffer, "w") as archive:
            archive.writestr("lean-build-metrics.json", json.dumps(record))
        return buffer.getvalue()

    def test_collect_filters_branches_and_reads_artifacts(self):
        def fake_fetch(url, token):
            self.assertEqual(token, "token")
            if url.endswith("/123/zip"):
                return self.archive(self.record)
            artifacts = [self.artifact, {**self.artifact, "workflow_run": {
                **self.artifact["workflow_run"], "head_branch": "feature"}}]
            return json.dumps({"artifacts": artifacts if self.repository in url else []}).encode()

        with patch.object(metrics, "fetch", side_effect=fake_fetch):
            self.assertEqual(metrics.collect("token"), [self.record])

    def test_rejects_mismatched_metadata(self):
        self.record["commit"] = "b" * 40
        with self.assertRaises(ValueError):
            metrics.parse_artifact(self.archive(self.record), self.repository, self.artifact)

    def test_paginates_and_skips_expired_artifacts(self):
        requests = []

        def fake_fetch(url, token):
            requests.append(url)
            page = urllib.parse.parse_qs(urllib.parse.urlsplit(url).query)["page"]
            if self.repository in url and page == ["1"]:
                return json.dumps({"artifacts": [{**self.artifact, "expired": True}] * 100}).encode()
            return b'{"artifacts": []}'

        with patch.object(metrics, "fetch", side_effect=fake_fetch):
            self.assertEqual(metrics.collect("token"), [])
        self.assertTrue(any(
            self.repository in url
            and urllib.parse.parse_qs(urllib.parse.urlsplit(url).query)["page"] == ["2"]
            for url in requests
        ))

    def test_removes_token_on_external_redirect(self):
        request = urllib.request.Request(
            "https://api.github.com/artifact", headers={"Authorization": "Bearer secret"}
        )
        redirect = metrics.SafeRedirect().redirect_request(
            request, None, 302, "Found", {}, "https://storage.example/file"
        )
        self.assertIsNone(redirect.get_header("Authorization"))
        with self.assertRaises(ValueError):
            metrics.SafeRedirect().redirect_request(
                request, None, 302, "Found", {}, "http://api.github.com/file"
            )


if __name__ == "__main__":
    unittest.main()
