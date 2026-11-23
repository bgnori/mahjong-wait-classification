#!/usr/bin/env python3

import io
import json
import math
import os
import re
import sys
import urllib.error
import urllib.parse
import urllib.request
import zipfile
from pathlib import Path


REPOSITORIES = (
    "bgnori/mahjong-domain-core",
    "bgnori/mahjong-shanten-calculation",
    "bgnori/mahjong-wait-classification",
)
ARTIFACT = "lean-build-metrics-v1"
MAX_BYTES = 1024 * 1024


class SafeRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        if urllib.parse.urlsplit(newurl).scheme != "https":
            raise ValueError("Artifact download redirect must use HTTPS")
        redirected = super().redirect_request(req, fp, code, msg, headers, newurl)
        if redirected and urllib.parse.urlsplit(req.full_url).netloc != urllib.parse.urlsplit(newurl).netloc:
            redirected.remove_header("Authorization")
        return redirected


def fetch(url: str, token: str) -> bytes:
    request = urllib.request.Request(
        url,
        headers={
            "Authorization": f"Bearer {token}",
            "Accept": "application/vnd.github+json",
            "X-GitHub-Api-Version": "2022-11-28",
        },
    )
    try:
        with urllib.request.build_opener(SafeRedirect()).open(request, timeout=30) as response:
            data = response.read(MAX_BYTES + 1)
    except urllib.error.HTTPError as error:
        raise RuntimeError(f"GitHub API or artifact download failed (HTTP {error.code})") from None
    except urllib.error.URLError:
        raise RuntimeError("GitHub API or artifact download failed") from None
    if len(data) > MAX_BYTES:
        raise ValueError("GitHub response exceeds the size limit")
    return data


def valid_metric(value) -> bool:
    return (
        isinstance(value, (int, float))
        and not isinstance(value, bool)
        and math.isfinite(value)
        and value >= 0
    )


def parse_artifact(data: bytes, repository: str, artifact: dict) -> dict:
    with zipfile.ZipFile(io.BytesIO(data)) as archive:
        names = archive.namelist()
        if names != ["lean-build-metrics.json"]:
            raise ValueError(f"{repository}: unexpected artifact contents")
        info = archive.getinfo(names[0])
        if info.file_size > MAX_BYTES:
            raise ValueError(f"{repository}: metrics file exceeds the size limit")
        record = json.loads(archive.read(info))
    run = artifact["workflow_run"]
    modules = record.get("modulePeakPssMiB")
    if (
        record.get("schemaVersion") != 1
        or record.get("repository") != repository
        or record.get("commit") != run["head_sha"]
        or str(record.get("runId")) != str(run["id"])
        or record.get("exitCode") != 0
        or not isinstance(record.get("startedAt"), str)
        or not isinstance(record.get("leanToolchain"), str)
        or not isinstance(record.get("coreCommit"), str)
        or not re.fullmatch(r"[0-9a-f]{40,64}", record["coreCommit"])
        or not re.fullmatch(r"[0-9a-f]{40,64}", record["commit"])
        or (record.get("peakTreePssMiB") is not None
            and not valid_metric(record["peakTreePssMiB"]))
        or not valid_metric(record.get("elapsedSeconds"))
        or not isinstance(modules, dict)
        or any(not isinstance(k, str) or (v is not None and not valid_metric(v))
               for k, v in modules.items())
    ):
        raise ValueError(f"{repository}: invalid metrics in artifact {artifact['id']}")
    return record


def collect(token: str) -> list[dict]:
    records = []
    for repository in REPOSITORIES:
        page = 1
        while True:
            url = (f"https://api.github.com/repos/{repository}/actions/artifacts"
                   f"?name={ARTIFACT}&per_page=100&page={page}")
            artifacts = json.loads(fetch(url, token))["artifacts"]
            for artifact in artifacts:
                if artifact["expired"] or artifact["workflow_run"]["head_branch"] != "main":
                    continue
                url = f"https://api.github.com/repos/{repository}/actions/artifacts/{artifact['id']}/zip"
                records.append(parse_artifact(fetch(url, token), repository, artifact))
            if len(artifacts) < 100:
                break
            page += 1
    return sorted(records, key=lambda record: record["startedAt"])


def main() -> None:
    token = os.environ.get("METRICS_TOKEN")
    if not token:
        raise RuntimeError("METRICS_TOKEN is required to read cross-repository artifacts")
    if len(sys.argv) != 2:
        raise SystemExit("usage: collect_build_metrics.py OUTPUT")
    output = Path(sys.argv[1])
    output.parent.mkdir(parents=True, exist_ok=True)
    records = collect(token)
    output.write_text(json.dumps(records, ensure_ascii=False) + "\n", encoding="utf-8")
    print(f"Collected {len(records)} Lean build metric records.")


if __name__ == "__main__":
    main()
