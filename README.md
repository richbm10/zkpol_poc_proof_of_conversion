# ZK Proof of Location — PoC

A Zero Knowledge circuit that proves a geographic coordinate lies inside a specific polygon belonging to a known set of authorized zones — without revealing the exact coordinate.

Built with [Circom 2.0.0](https://docs.circom.io/) and [Groth16](https://eprint.iacr.org/2016/260) via [snarkjs](https://github.com/iden3/snarkjs). Originally developed as a PoC for the PES Hackathon.

---

## How It Works

The circuit, `ValidateCoordinateInclusion`, simultaneously proves three things in a single ZK proof:

1. **Point-in-polygon** — the coordinate `(px, py)` lies inside a given polygon, using a ray casting algorithm.
2. **Polygon integrity** — the polygon's Poseidon hash matches the claimed `polygonHash`.
3. **Authorized zone** — the polygon belongs to a known Merkle tree of authorized polygons, verified against a public `root`.

The polygon vertices are **private inputs**, so a verifier only learns that the prover was inside _some_ authorized zone, not which polygon or where exactly.

```
Prover knows:            Public (on-chain or shared):
  (px, py)               root (Merkle root of all zones)
  polygon[4][2]          polygonHash
  Merkle path            isValid = 1
```

---

## Circuit Parameters

The main component is instantiated as:

```circom
component main = ValidateCoordinateInclusion(16, 4, 32);
```

| Parameter   | Value | Meaning                              |
|-------------|-------|--------------------------------------|
| `depth`     | 16    | Merkle tree depth (supports 2^16 polygons) |
| `n`         | 4     | Number of polygon vertices           |
| `grid_bits` | 32    | Coordinate bit width (max 2^32)      |

### Inputs

| Signal              | Visibility | Description                                 |
|---------------------|------------|---------------------------------------------|
| `px`, `py`          | Public     | Shifted coordinate to prove                 |
| `polygonHash`       | Public     | Poseidon hash of the polygon                |
| `root`              | Public     | Merkle root of authorized polygons          |
| `pathIndices[16]`   | Public     | Merkle proof path direction (0=left,1=right)|
| `pathElements[16]`  | Public     | Merkle proof sibling hashes                 |
| `polygon[4][2]`     | Private    | Raw polygon vertex coordinates              |

### Output

| Signal    | Description                            |
|-----------|----------------------------------------|
| `isValid` | `1` if all three checks pass, else `0` |

---

## Coordinate System

Real GPS coordinates must be converted to a strictly-positive integer grid before use:

```
shifted_lat  = (latitude  + 90)  * 1_000_000
shifted_long = (longitude + 180) * 1_000_000
```

This maps latitudes to `[0, 180_000_000]` and longitudes to `[0, 360_000_000]`, both safely within `grid_bits=32` (max 4,294,967,296).

**Example — Krispy Kreme, Escazu, Costa Rica:**
```
lat  ≈  9.930794°  →  px = 99_930_794
long ≈ -84.149014° →  py = 95_850_986
```

---

## Prerequisites

```bash
# Install circom
curl --proto '=https' --tlsv1.2 https://sh.rustup.rs -sSf | sh
git clone https://github.com/iden3/circom.git && cd circom
cargo build --release && cargo install --path circom

# Install snarkjs
npm install -g snarkjs

# Install circomlib
npm install circomlib
```

---

## Usage

### 1. Compile the circuit

```bash
circom ProofOfLocation.circom --r1cs --wasm --sym -o ./build
```

### 2. Trusted setup (Groth16 — run once)

```bash
snarkjs powersoftau new bn128 16 pot16_0000.ptau
snarkjs powersoftau contribute pot16_0000.ptau pot16_0001.ptau --name="contributor"
snarkjs powersoftau prepare phase2 pot16_0001.ptau pot16_final.ptau

snarkjs groth16 setup build/ProofOfLocation.r1cs pot16_final.ptau circuit_0000.zkey
snarkjs zkey contribute circuit_0000.zkey circuit_final.zkey --name="contributor"
snarkjs zkey export verificationkey circuit_final.zkey verification_key.json
```

### 3. Prepare input

Create `input.json` with the shifted coordinates, polygon, and Merkle proof. A sample input is embedded at the bottom of `ProofOfLocation.circom` (the Escazu location).

### 4. Generate witness and proof

```bash
# Generate witness
node build/ProofOfLocation_js/generate_witness.js \
  build/ProofOfLocation_js/ProofOfLocation.wasm \
  input.json witness.wtns

# Generate proof
snarkjs groth16 fullprove \
  input.json \
  build/ProofOfLocation_js/ProofOfLocation.wasm \
  circuit_final.zkey \
  proof.json public.json
```

### 5. Verify

```bash
snarkjs groth16 verify verification_key.json public.json proof.json
```

---

## Sample Input

The circuit file includes a working test input for a point inside a small polygon near Krispy Kreme, Escazu, Costa Rica:

```json
{
  "px": "99930794",
  "py": "95850986",
  "polygonHash": "19734256724370939262826947009735877839971681289001157384192434648867876200933",
  "polygon": [
    ["99930607", "95850886"],
    ["99930856", "95851062"],
    ["99930840", "95850853"],
    ["99930610", "95851072"]
  ],
  "root": "2703440162454052840609636720528243608663031709412357648362337729401815863073",
  "pathIndices": ["0","1","0","1","0","1","0","1","0","1","0","1","0","1","0","1"],
  "pathElements": [
    "19734256724370939262826947009735877839971681289001157384192434648867876200933",
    "2222222222222222222222222222222222222222222222222222222222222222",
    ...
  ]
}
```

A nearby point that falls **outside** the polygon is also referenced in the source:
```
Costa Rica, Escazu (outside): px=99931080, py=95851137
```

---

## References

- [zkMaps](https://github.com/zkMaps/zkMaps/tree/main) — reference implementation for ZK geometric primitives
- [circomlib](https://github.com/iden3/circomlib) — standard Circom circuit library (comparators, Poseidon, bitify)
- [Circom docs](https://docs.circom.io/)
- [snarkjs](https://github.com/iden3/snarkjs)
