# A proof-irrelevant model for System F Omega in Coq
A simple proof-irrelevant model for System F Omega (PTS with type-level computation and polymorphism, but without dependent types) mechanized in Coq. 

To model impredicativity, types are mapped to Coq's impredicative `Prop`. The proof itself is intuitive on paper, but the shallow embedding from type-level lambdas to Coq functions requires writing and reasoning about dependently typed programs, something that I believe is impossible to avoid, unlike semantic models for predicative systems.

The semantic model can be extended to show strong normalization of System F Omega or even Calculus of Constructions since there's a known translation from CoC to F Omega. However, for now, I'm quite content with being able to prove that $\forall X. X$ is not inhabited (see [false_imp](https://github.com/yiyunliu/system-f-omega/blob/fomega/theories/semantics.v#L450)) for an impredicative system that supports type-level reduction.

# Dependencies
- coq-hammer-tactics 1.3.2
- stdpp 1.10.0
- coq 8.19.2
- coq-equations 1.3
