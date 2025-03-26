# There are finitely many 5-vertex-critical (P6,bull)-free graphs

This repository contains code and data related to the paper "There are finitely many 5-vertex-critical (P6,bull)-free graphs". In this paper, we verify 10 claims with the help of a computer. Each claim has a separate directory. We will illustrate for one of the folders below how to verify the claims again and obtain the 5-vertex-critical graphs.

## ComplementC7
Go to the directory "ComplementC7":
```bash
cd ComplementC7/
```

Compile the C program for generating the 5-vertex-critical graphs:
```bash
make
```

The claim can be verified by executing the following python program (which will internally call the C program):

```bash
python3 verifyClaim.py
```

After the program terminates, several statistics will be printed about the program. Note that for some claims, it may take several days before the program terminates. The 5-vertex-critical graphs can be found in the file "allVertexCritical.g6" after the program terminates. These graphs are encoded in graph6 format.
