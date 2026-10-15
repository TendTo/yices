# syntax=docker/dockerfile:1.19

# -------- Builder stage --------
FROM ubuntu:24.04 AS builder

ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update && apt-get install -y --no-install-recommends \
    build-essential \
    ca-certificates \
    cmake \
    ninja-build \
    git \
    curl \
    pkg-config \
    python3 \
    zstd \
    libgmp-dev \
    python3-venv \
    libtool \
    libz-dev \
    libboost-all-dev \
    libmpfr-dev \
    libbz2-dev \
    gperf \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /src

#RUN git clone https://github.com/TendTo/soplex.git -b soplex-master --depth 1 \
#    && cd /src/soplex

RUN git clone https://github.com/TendTo/soplex.git -b soplex-master --depth 1 \
    && cd /src/soplex \
    && git checkout 4a33bbd0801f89d8ba7343061412b2cc7d35914c \
    && cmake -S . -B build -DCMAKE_BUILD_TYPE=Release -DGMP=ON -DMPFR=ON -DBOOST=ON -DLIGHT_RAT=ON -DZLIB=OFF -DBUILD_TESTING=OFF \
    && cd build \
    && make -j"$(nproc)" libsoplex \
    && make install

RUN git clone https://github.com/TendTo/qsopt-ex.git --depth 1 \
    && cd /src/qsopt-ex \
    && git checkout 69b0b59e4c193b6cb4e11c2ec521424e2b2efcb7 \
    && ./bootstrap \
    && mkdir build && cd build \
    && ../configure --disable-debug \
    && make -j"$(nproc)" \
    && make install

RUN mv /usr/local/lib/libsoplexshared.so.9.0 /usr/local/lib/libsoplex.so

WORKDIR /src/yices

COPY . /src/yices

# Configure and build yices as a static binary.
RUN autoconf \
    && ./configure --enable-qsoptex --enable-soplex \
    && make -j"$(nproc)" MODE=release static-bin

ENTRYPOINT ["/bin/bash"]

# -------- Runtime stage --------
FROM alpine:3 AS runtime

LABEL org.opencontainers.image.authors="Ernesto Casablanca"
LABEL author="Ernesto Casablanca"

COPY --from=builder --chmod=777 /src/yices/build/x86_64-pc-linux-gnu-release/static_bin/yices_smt2 /usr/local/bin/yices_smt2

ENTRYPOINT ["yices_smt2"]
