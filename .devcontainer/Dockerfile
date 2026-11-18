# ============================================
# Lean 4 DevContainer Dockerfile
# Base: debian:bookworm-slim (~70MB)
# Includes Google Cloud CLI for remote computation management.
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
    gnupg \
    build-essential \
    procps \
    sudo \
    time \
    tmux \
    python3 \
    && rm -rf /var/lib/apt/lists/* \
    && apt-get clean

RUN curl -fsSL https://packages.cloud.google.com/apt/doc/apt-key.gpg \
      -o /tmp/google-cloud-apt-key.gpg \
    && gpg --dearmor -o /usr/share/keyrings/cloud.google.gpg /tmp/google-cloud-apt-key.gpg \
    && rm /tmp/google-cloud-apt-key.gpg \
    && echo "deb [signed-by=/usr/share/keyrings/cloud.google.gpg] https://packages.cloud.google.com/apt cloud-sdk main" \
      > /etc/apt/sources.list.d/google-cloud-sdk.list \
    && apt-get update \
    && apt-get install -y --no-install-recommends google-cloud-cli \
    && gcloud --version \
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
