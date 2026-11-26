#!/usr/bin/env bash
# Fetch kubernetes at the pinned SHA into go/upstream (blobless, sparse: staging/src/k8s.io only).
set -euo pipefail
cd "$(dirname "$0")"
SHA=dbe731cf4b0286d68d743068f251263c70719f3e
if [ -d upstream/.git ] && [ "$(git -C upstream rev-parse HEAD 2>/dev/null)" = "$SHA" ]; then
  echo "upstream already at $SHA"; exit 0
fi
rm -rf upstream
git init -q upstream
cd upstream
git remote add origin https://github.com/kubernetes/kubernetes.git
git config extensions.partialClone origin
git sparse-checkout init --cone
git sparse-checkout set staging/src/k8s.io
git fetch -q --depth 1 --filter=blob:none origin "$SHA"
git checkout -q FETCH_HEAD
git rev-parse HEAD
