# ============================================
# Lean 4 DevContainer Dockerfile
# Base: debian:bookworm-slim (~70MB)
#
# Host resources are selected by Codespaces from the chosen devcontainer profile.
# Do not impose Docker CPU or memory limits inside this image.
# ============================================

FROM debian:bookworm-slim

# Install minimal required packages
RUN apt-get update && apt-get install -y --no-install-recommends \
    curl \
    ca-certificates \
    git \
    build-essential \
    procps \
    sudo \
    time \
    tmux \
    python3 \
    && rm -rf /var/lib/apt/lists/* \
    && apt-get clean

# Set environment variables for elan
ENV ELAN_HOME=/usr/local/elan \
    PATH=/usr/local/elan/bin:$PATH

RUN curl --proto '=https' --tlsv1.2 -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o /tmp/elan-init.sh \
    && sh /tmp/elan-init.sh -y --no-modify-path --default-toolchain none \
    && rm /tmp/elan-init.sh

COPY lean-toolchain /tmp/lean-toolchain
RUN toolchain="$(cat /tmp/lean-toolchain)" \
    && elan toolchain install "$toolchain" \
    && elan default "$toolchain" \
    && rm /tmp/lean-toolchain

WORKDIR /workspace
