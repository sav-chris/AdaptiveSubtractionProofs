FROM ubuntu:22.04

# Install dependencies
RUN apt-get update && apt-get install -y \
    curl \
    git \
    unzip \
    xz-utils \
    libgmp-dev \
    build-essential \
    zstd \
    && rm -rf /var/lib/apt/lists/*

# Create user
RUN useradd -ms /bin/bash lean
USER lean
WORKDIR /home/lean

# Install elan (Lean version manager)
RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
ENV PATH="/home/lean/.elan/bin:${PATH}"

# Download and install Lean toolchain manually (bypassing elan download)
RUN curl -L https://releases.lean-lang.org/lean4/v4.21.0/lean-4.21.0-linux.tar.zst -o lean-4.21.0-linux.tar.zst \
    && mkdir /home/lean/lean-toolchain \
    && tar -I zstd -xvf lean-4.21.0-linux.tar.zst -C /home/lean/lean-toolchain

WORKDIR /home/lean/proofs/my_project
