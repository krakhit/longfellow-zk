# Complete Backend Prover Workflow in Longfellow ZK

```mermaid
flowchart TD
    subgraph "Input Preparation"
        A1[Compiled Circuit<br/>From Frontend]
        A2[Witness Values<br/>Public + Private]
        A3[Prover Parameters<br/>Field, ReedSolomon]
    end
    
    subgraph "ZK Prover Initialization"
        B1[ZkProver Constructor<br/>Circuit + Field + RSFactory]
        B2[Witness Separation<br/>Public vs Private]
        B3[Subfield Boundary<br/>Detection]
        B4[Pad Structure Setup<br/>Per-layer padding]
    end
    
    subgraph "Commitment Phase"
        C1[Random Padding Generation<br/>fill_pad()]
        C2[Witness Extension<br/>Add padding to witness]
        C3[LQC Setup<br/>Ligero Quadratic Constraints]
        C4[Ligero Prover Creation<br/>LigeroProver instance]
        C5[Merkle Commitment<br/>Commit to witness+pad]
    end
    
    subgraph "Circuit Evaluation"
        D1[Input Wire Assignment<br/>Dense array setup]
        D2[Layer-by-Layer Evaluation<br/>eval_circuit()]
        D3[Quad Gate Evaluation<br/>eval_quad()]
        D4[Wire Value Propagation<br/>Forward computation]
        D5[Output Validation<br/>Check all outputs = 0]
    end
    
    subgraph "Sumcheck Protocol"
        E1[Fiat-Shamir Initialization<br/>Public inputs to transcript]
        E2[Transcript Cloning<br/>Separate transcript]
        E3[ProverLayers.prove()<br/>Sumcheck execution]
        E4[Layer Processing<br/>For each circuit layer]
        E5[Binding Operations<br/>Copy + Wire variables]
        E6[Polynomial Generation<br/>CPoly + WPoly]
        E7[Challenge Response<br/>Evaluate at random points]
        E8[Proof Generation<br/>Padded sumcheck proof]
    end
    
    subgraph "Verifier Simulation"
        F1[ZkCommon.verifier_constraints()<br/>Simulate verifier]
        F2[Challenge Regeneration<br/>Replay Fiat-Shamir]
        F3[Constraint Assembly<br/>Linear constraints Ax=b]
        F4[Sumcheck Verification<br/>Check transcript consistency]
        F5[Binding Verification<br/>Input wire constraints]
    end
    
    subgraph "Ligero Proof Generation"
        G1[Constraint Matrix A<br/>From verifier simulation]
        G2[Constraint Vector b<br/>Expected values]
        G3[Hash of Constraints<br/>For theorem statement]
        G4[Ligero Prove<br/>lp_->prove()]
        G5[Low-Degree Test<br/>Polynomial degree verification]
        G6[Dot Product Test<br/>Linear constraint verification]
        G7[Quadratic Test<br/>Quadratic constraint verification]
        G8[Column Opening<br/>Random column reveals]
    end
    
    subgraph "Proof Assembly"
        H1[Sumcheck Proof<br/>Layer polynomials + claims]
        H2[Ligero Proof<br/>Tableau openings + tests]
        H3[Commitment Data<br/>Merkle root + parameters]
        H4[ZkProof Assembly<br/>Complete proof structure]
        H5[Proof Serialization<br/>Ready for transmission]
    end
    
    A1 --> B1
    A2 --> B2
    A3 --> B1
    
    B1 --> B2
    B2 --> B3
    B3 --> B4
    
    B4 --> C1
    C1 --> C2
    C2 --> C3
    C3 --> C4
    C4 --> C5
    
    C5 --> D1
    D1 --> D2
    D2 --> D3
    D3 --> D4
    D4 --> D5
    
    D5 --> E1
    E1 --> E2
    E2 --> E3
    E3 --> E4
    E4 --> E5
    E5 --> E6
    E6 --> E7
    E7 --> E8
    
    E8 --> F1
    F1 --> F2
    F2 --> F3
    F3 --> F4
    F4 --> F5
    
    F5 --> G1
    G1 --> G2
    G2 --> G3
    G3 --> G4
    G4 --> G5
    G5 --> G6
    G6 --> G7
    G7 --> G8
    
    G8 --> H1
    H1 --> H2
    H2 --> H3
    H3 --> H4
    H4 --> H5
    
    classDef input fill:#fff3e0
    classDef init fill:#e3f2fd
    classDef commit fill:#f1f8e9
    classDef eval fill:#fce4ec
    classDef sumcheck fill:#f3e5f5
    classDef simulate fill:#e0f2f1
    classDef ligero fill:#fff8e1
    classDef assembly fill:#f0f4c3
    
    class A1,A2,A3 input
    class B1,B2,B3,B4 init
    class C1,C2,C3,C4,C5 commit
    class D1,D2,D3,D4,D5 eval
    class E1,E2,E3,E4,E5,E6,E7,E8 sumcheck
    class F1,F2,F3,F4,F5 simulate
    class G1,G2,G3,G4,G5,G6,G7,G8 ligero
    class H1,H2,H3,H4,H5 assembly
```

## Detailed Backend Workflow

### Input Preparation
- **Compiled Circuit**: Output from frontend arithmetization
- **Witness Values**: Concrete values for all circuit inputs
- **Prover Parameters**: Field type, Reed-Solomon factory, security parameters

### ZK Prover Initialization
```cpp
template <class Field, class ReedSolomonFactory>
class ZkProver : public ProverLayers<Field> {
  ZkProver(const Circuit<Field>& circuit, const Field& F, 
           const ReedSolomonFactory& rs_factory);
  
  // Separate private witnesses from public inputs
  const size_t n_witness_ = circuit.ninputs - circuit.npub_in;
};
```

### Commitment Phase
```cpp
void ZkProver::commit(ZkProof<Field>& zkp, const Dense<Field>& W,
                      Transcript& tp, RandomEngine& rng) {
  // 1. Copy private witnesses
  for (size_t i = 0; i < n_witness_; ++i) {
    witness_[i] = W.v_[i + c_.npub_in];
  }
  
  // 2. Generate random padding
  fill_pad(rng);
  
  // 3. Setup Ligero quadratic constraints
  ZkCommon<Field>::setup_lqc(c_, lqc_, n_witness_);
  
  // 4. Commit using Ligero
  lp_->commit(zkp.com, tp, &witness_[0], subfield_boundary, 
              &lqc_[0], rsf_, rng, f_);
}
```

### Random Padding Generation
```cpp
void ZkProver::fill_pad(RandomEngine& rng) {
  for (size_t layer = 0; layer < c_.nl; ++layer) {
    // Pad copy polynomials (degree 3)
    for (size_t j = 0; j < c_.logc; ++j) {
      for (size_t k = 0; k < 4; ++k) {
        if (k != 1) {  // P(1) optimization
          pad_.l[layer].cp[j].t_[k] = rng.elt(f_);
          witness_.push_back(pad_.l[layer].cp[j].t_[k]);
        }
      }
    }
    
    // Pad wire polynomials (degree 2)
    for (size_t j = 0; j < c_.l[layer].logw; ++j) {
      for (size_t hand = 0; hand < 2; ++hand) {
        for (size_t k = 0; k < 3; ++k) {
          if (k != 1) {  // P(1) optimization
            pad_.l[layer].hp[hand][j].t_[k] = rng.elt(f_);
            witness_.push_back(pad_.l[layer].hp[hand][j].t_[k]);
          }
        }
      }
    }
    
    // Pad final claims
    for (size_t k = 0; k < 2; ++k) {
      pad_.l[layer].wc[k] = rng.elt(f_);
      witness_.push_back(pad_.l[layer].wc[k]);
    }
    
    // Commit to product for quadratic constraints
    Elt product = f_.mulf(pad_.l[layer].wc[0], pad_.l[layer].wc[1]);
    witness_.push_back(product);
  }
}
```

### Circuit Evaluation
```cpp
std::unique_ptr<Dense<Field>> ProverLayers::eval_circuit(
    inputs* in, const Circuit<Field>* circ,
    std::unique_ptr<Dense<Field>> W0, const Field& F) {
  
  // Evaluate each layer from inputs to outputs
  for (size_t layer = circ->nl; layer-- > 0;) {
    Dense<Field>* input_wires = W;
    Dense<Field>* output_wires = V;
    
    // Evaluate quadratic gates: V[g] = ∑ᵢ vᵢ * W[lᵢ] * W[rᵢ]
    bool ok = eval_quad(circ->l[layer].quad.get(), output_wires, 
                       input_wires, F);
    if (!ok) return nullptr;  // Assertion failure
    
    W = V;  // Output becomes input for next layer
  }
  
  return finalV;
}
```

### Sumcheck Protocol Execution
```cpp
void ProverLayers::prove(Proof<Field>* pr, const Proof<Field>* pad,
                        const Circuit<Field>* circ, const inputs& in,
                        ProofAux<Field>* aux, bindings& bnd,
                        TranscriptSumcheck<Field>& ts, const Field& F) {
  
  // Initialize with verifier challenges
  ts.begin_circuit(bnd.q, bnd.g[0]);
  
  // Process each circuit layer
  for (size_t layer = 0; layer < circ->nl; ++layer) {
    Elt alpha, beta;
    ts.begin_layer(alpha, beta, layer);
    
    // Setup equality check and quad gates
    Eqs<Field> EQ(logc, nc, bnd.q, F);
    auto QUAD = clr->quad->clone();
    QUAD->bind_g(bnd.logv, bnd.g[0], bnd.g[1], alpha, beta, F);
    
    // Execute sumcheck for this layer
    layer(pr, pad, ts, bnd, layer, logc, clr->logw, 
          &EQ, QUAD.get(), in.at(layer).get(), F);
  }
}
```

### Layer-by-Layer Sumcheck
```cpp
void ProverLayers::layer(/* parameters */) {
  // Bind copy variables (C dimension)
  for (size_t round = 0; round < logc; ++round) {
    // Compute polynomial ∑ᵣ,ₗ QUAD[r,l] EQ[c] W[r,c] W[l,c]
    CPoly sum = compute_copy_polynomial(QUAD, EQ, W, F);
    
    // Send polynomial (subtract padding if ZK)
    Elt challenge = round_c(pr, pad, ts, layer, round, sum, F);
    
    // Bind copy variable
    bnd.q[round] = challenge;
    EQ->bind(challenge, F);
    W->bind(challenge, F);
  }
  
  // Bind wire variables (R, L dimensions)
  for (size_t round = 0; round < logw; ++round) {
    for (size_t hand = 0; hand < 2; ++hand) {
      // Compute polynomial ∑ₗ QW[l] W[l] where QW[l] = ∑ᵣ Q[l,r] W[r]
      WPoly sum = compute_wire_polynomial(QUAD, W, hand, F);
      
      // Send polynomial (subtract padding if ZK)
      Elt challenge = round_h(pr, pad, ts, layer, hand, round, sum, F);
      
      // Bind wire variable
      bnd.g[hand][round] = challenge;
      W->bind(challenge, F);
      QUAD->bind_h(challenge, hand, F);
    }
  }
  
  // Final claims for next layer
  Elt wc[2] = {W_left->scalar(), W_right->scalar()};
  end_layer(pr, pad, ts, layer, wc, F);
}
```

### Verifier Simulation
```cpp
size_t ZkCommon::verifier_constraints(
    const Circuit<Field>& circuit, const Dense<Field>& pub,
    const Proof<Field>& proof, const ProofAux<Field>* aux,
    std::vector<LigeroLinearConstraint<Field>>& a,
    std::vector<Elt>& b, Transcript& tsv, size_t pi, const Field& F) {
  
  // Replay the sumcheck verifier algorithm
  Challenge<Field> ch(circuit.nl);
  TranscriptSumcheck<Field> tss(tsv, F);
  
  // For each layer, generate constraints that the Ligero system
  // will verify on the committed witness
  for (size_t layer = 0; layer < circuit.nl; ++layer) {
    // Generate challenges from transcript
    tss.begin_layer(challenge->alpha, challenge->beta, layer);
    
    // Build symbolic constraint: claim = EQ[Q,C] QUAD[R,L] W[R,C] W[L,C]
    ConstraintBuilder cb(pad_layout, F);
    
    // ... constraint building logic ...
    
    // Add constraint to Ligero system
    cb.finalize(proof_layer->wc, expected_value, constraint_index,
                layer, pad_index, a, b);
  }
  
  return constraint_count;
}
```

### Ligero Proof Generation
```cpp
void LigeroProver::prove(LigeroProof<Field>& proof, Transcript& ts,
                        size_t nl, size_t nllterm,
                        const LigeroLinearConstraint<Field> llterm[],
                        const LigeroHash& hash_of_llterm,
                        const LigeroQuadraticConstraint lqc[],
                        const InterpolatorFactory& interpolator,
                        const Field& F) {
  
  // 1. Low-degree test
  std::vector<Elt> u_ldt(p_.nwqrow);
  LigeroTranscript<Field>::gen_uldt(&u_ldt[0], p_, ts, F);
  low_degree_proof(&proof.y_ldt[0], &u_ldt[0], F);
  
  // 2. Linear constraint test  
  std::vector<Elt> alphal(nl);
  std::vector<std::array<Elt, 3>> alphaq(p_.nq);
  LigeroTranscript<Field>::gen_alphal(nl, &alphal[0], ts, F);
  LigeroTranscript<Field>::gen_alphaq(&alphaq[0], p_, ts, F);
  
  std::vector<Elt> A(p_.nwqrow * p_.w);
  LigeroCommon<Field>::inner_product_vector(&A[0], p_, nl, nllterm,
                                           llterm, &alphal[0], lqc,
                                           &alphaq[0], F);
  dot_proof(&proof.y_dot[0], &A[0], interpolator, F);
  
  // 3. Quadratic constraint test
  std::vector<Elt> u_quad(p_.nqtriples);
  LigeroTranscript<Field>::gen_uquad(&u_quad[0], p_, ts, F);
  quadratic_proof(&proof.y_quad_0[0], &proof.y_quad_2[0], &u_quad[0], F);
  
  // 4. Column opening
  std::vector<size_t> idx(p_.nreq);
  LigeroTranscript<Field>::gen_idx(&idx[0], p_, ts, F);
  compute_req(proof, &idx[0]);
  mc_.open(proof.merkle, &idx[0], p_.nreq);
}
```

### Proof Assembly
Final proof structure:
```cpp
template <class Field>
struct ZkProof {
  LigeroParam<Field> param;           // Ligero parameters
  LigeroCommitment<Field> com;        // Merkle commitment
  Proof<Field> proof;                 // Sumcheck proof
  LigeroProof<Field> com_proof;       // Ligero SNARK proof
};
```

## Key Performance Optimizations

### P(1) Optimization
- Set polynomial evaluations at point 1 to zero
- Reduces proof size by ~25% with no security loss
- Implemented throughout padding generation

### Subfield Optimization  
- Use smaller field elements when possible
- Reduces commitment size for bit-valued witnesses
- Automatically detected during compilation

### Parallel Processing
- Layer evaluation can be parallelized
- Multiple copies enable batch verification
- SIMD operations in field arithmetic

### Memory Efficiency
- Streaming evaluation avoids storing full witness
- Reuse arrays between layers
- Compressed proof serialization 