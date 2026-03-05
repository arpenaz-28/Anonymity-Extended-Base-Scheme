# Lightweight Decoupled Distributed PUF-Based Authentication for Multihop IoT Networks

A lightweight and decoupled distributed authentication scheme for resource-constrained multihop IoT networks, built on **Contiki-NG** and evaluated via **COOJA simulation**.

---

## Overview

This scheme enables newly joined IoT devices to authenticate with the network through designated **Authentication Servers (AS)** — any node authorized by the gateway — rather than relying solely on parent nodes. It uses:

- **PUF (Physically Unclonable Function)** — hardware-based challenge-response for device-specific authentication without long-term key storage
- **Hash-based AND Accumulator** — O(1) membership verification using bitwise AND over hashed secrets
- **Rotating Pseudonyms** — `PID = H(ID || m)` updated each session for device anonymity and unlinkability
- **Session-based Randoms** — mask values rotated after each authentication to prevent replay and interception

## Protocol Phases

| Phase | Direction | Description |
|-------|-----------|-------------|
| **1. Enrollment** | D ↔ AS | Device registers its hashed secret `Y = H(y)` into the accumulator `T_acc &= Y`. PUF binding `Φ = R_AS ⊕ R_D` stored for later recovery. |
| **2. Authentication** | D → AS | Device sends `PID \| Y⊕mask \| ts₁` (65 B). AS recovers `Y` via PUF binding, verifies `T_acc & Y == T_acc`. |
| **3. Key Exchange** | AS → D, AS → GW | AS generates session key `K = H(R_D \|\| m_new)`, sends masked `m_new` to device and encrypted auth token to gateway. |

After key exchange, the device communicates directly with the gateway using `SE(K_GW-D, data)`.

## Project Structure

```
├── device-node.c      # IoT device — enrollment, auth, data transmission
├── as-node.c           # Authentication server — accumulator, PUF binding, key generation
├── gw-node.c           # Gateway — RPL root, token processing, data decryption
├── aes.c / aes.h       # AES-128-ECB encryption
├── sha256.c / sha256.h # SHA-256 hashing
├── project-conf.h      # Network configuration (node IDs, energest, CoAP)
├── Makefile            # Contiki-NG build system
└── Proposed_Scheme_Paper.docx  # Full paper with sequence diagrams
```

## Simulation Results (100-node COOJA)

| Metric | Result |
|--------|--------|
| Devices enrolled & authenticated | 20/20 (100%) |
| Data messages confirmed by GW | 347 |
| Per-device auth energy | 0.019 – 0.036 J |
| Computational cost | **0.56 ms** (2 PUF + 8 hash + 2 AES) |
| Communication cost | **928 bits** (3 messages) |

## Security Properties

- **Replay resistance** — timestamp freshness + session random rotation
- **MITM resistance** — PUF-based masking + encrypted enrollment channel
- **Device anonymity** — rotating pseudonyms, unlinkable across sessions
- **Desync recovery** — dual PID/random storage (`curr` + `old`)
- **Forward secrecy** — session key derived from fresh random each time

## Build & Run

Requires [Contiki-NG](https://github.com/contiki-ng/contiki-ng) with COOJA simulator (Docker recommended):

```bash
# Build firmware
make TARGET=cooja

# Run simulation (headless)
cd tools/cooja && ./gradlew run --args='--no-gui --autostart <csc-file>'
```

## License

Academic use — Master's Thesis Project (MTP).
