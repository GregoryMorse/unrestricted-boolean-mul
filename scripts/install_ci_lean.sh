#!/usr/bin/env bash
# Exact official release asset, independently pinned by SHA-256. This avoids
# the release-proxy TLS failures seen on GitHub runners; never disable TLS.
set -euo pipefail
expected='leanprover/lean4:v4.35.0-rc3'
actual=$(tr -d '\r\n' < lean-toolchain)
if [[ "$actual" != "$expected" || "$(uname -sm)" != 'Linux x86_64' ]]; then
  echo 'Unexpected toolchain or CI architecture' >&2
  exit 1
fi
asset="$RUNNER_TEMP/lean-4.35.0-rc3-linux.tar.zst"
prefix="$RUNNER_TEMP/lean-4.35.0-rc3-verified"
curl --fail --location --show-error --retry 3 --retry-all-errors --max-time 240 \
  'https://github.com/leanprover/lean4/releases/download/v4.35.0-rc3/lean-4.35.0-rc3-linux.tar.zst' \
  --output "$asset"
printf '%s  %s\n' '1526de16c0496f16b46a168f26c990af4e3796505273c3342fec17d72d763997' "$asset" | sha256sum --check --strict
mkdir -p "$prefix"
tar --zstd -xf "$asset" --strip-components=1 -C "$prefix"
printf '%s\n' "$prefix/bin" >> "$GITHUB_PATH"
"$prefix/bin/lean" --version
