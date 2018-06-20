# sharing

Coq formalization of proof soundness for "Tracing sharing in an imperative pure calculus"

Coq version 8.7.2 (March 2018)
coq-equations  1.0+8.7

## Contents

### AdditionalTactics.v
### Atom.v

  support for atoms with decidable equality providing
  the ability to generate an atom fresh for any finite
  collection (taken from Chargueraud/Aydemir)

### Connected.v

  predicate connectedDecs and function splitDecs -
  needed for garbage elimination

### DecidableEquivalences.v

  decidable equivalence relations, containment,
  operations addPair, pullback, addSingle and
  some properties of these

### DPF.v

  decidable prepositions and decidable predicates on
  Fin n

### EqR.v

  equivalence relations on Fin n as an inductive family;
  maps associated to an equivalence (element to class, class
  to maximal element, ...); 
  containment of equivalences, proven to be partial order; 
  map to decidable equivalences (preserving and reflecting 
  containment);  

### EqRMeet.v

  meet of equivalence relations (unfinished)

### EvaluationSimpl.v

  value predicate and (sub)type; alpha; substitution;
  block generation; evaluation contexts along with some
  predicates and functions

### FinVectorMisc.v

  auxiliary lemmata on Fins and Vectors

### Metatheory.v

  a number of auxiliary constructs (and their properties)
  for the study of programming languages in Coq (from "Cast-Free 
  Featherweight Java" by De Fraine, Ernst and Sudholt)

### NatMisc.v

  reprove some standard lemmata on Nat to have
  them transparent

### NotationsMisc.v

  notations

### SharingRelation.v

  defines sharing relations on a list l of variables
  as equivalences on Fin.t (length l);
  operations on sharing relations adding and removing
  connections (especially to res);
  restriction to sublist; addition; capsule property


### SigmaMisc.v

  lemmata for equality in sigma types

### TypedLanguageSimpl.v

  types the syntax of the calculus:
  calculus types, annotations, declarations, expressions, environments;
  some functions and predicates on these;
  definition of the typing relation



