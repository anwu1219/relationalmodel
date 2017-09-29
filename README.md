This program uses the relation-algebra library (https://github.com/coq-contribs/relation-algebra) to solve some relation algebra queries of the Hahn library (https://github.com/vafeiadis/hahn).
Specifically, it contains a tactic "kat_solve" that:
1. converts a Hahn query into a relation-algebra lib query.
2. calls the tactic "kat" in the relation-algebra library to solve the query.
