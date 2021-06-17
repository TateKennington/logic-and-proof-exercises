### Exercise 1  
| $A$ | $B$ | $A \rightarrow B$ | $\neg A \lor B$ | $\neg(A \land \neg B)$ |  
| :---: |  :---: |  :---: |  :---: |  :---: | 
| 0 | 0 | 1 | 1 | 1 |
| 0 | 0 | 1 | 1 | 1 |
| 0 | 1 | 1 | 1 | 1 |
| 1 | 0 | 0 | 0 | 0 |
| 1 | 1 | 1 | 1 | 1 |

### Exercise 2
|$A$ | $B$ | $C$ | $A \rightarrow B$ | $B \land C \rightarrow A$ | $(A \rightarrow B) \land (B \land C \rightarrow A)$ |
|:---:|:---:|:---:|:---:|:---:|:---:|
| 0 | 0 | 0 | 1 | 1 | 1 |
| 0 | 1 | 0 | 1 | 1 | 1 |
| 1 | 0 | 0 | 0 | 1 | 0 |
| 1 | 1 | 0 | 1 | 1 | 1 |
| 0 | 0 | 1 | 1 | 1 | 1 |
| 0 | 1 | 1 | 1 | 0 | 0 |
| 1 | 0 | 1 | 0 | 1 | 0 |
| 1 | 1 | 1 | 1 | 1 | 1 |

### Exercise 3
| $A$ | $B$ | $A \rightarrow B$ | $\neg B \rightarrow \neg A$ |
|:---:|:---:|:---:|:---:|
| 0 | 0 | 1 | 1 |
| 0 | 1 | 1 | 1 |
| 1 | 0 | 0 | 0 |
| 1 | 1 | 1 | 1 |

### Exercise 4
| $A$ | $B$ | $C$ | $A \rightarrow B \lor C$ | $\neg B \rightarrow \neg C$ | $A \rightarrow B$ |
|:---:|:---:|:---:|:---:|:---:|:---:|
| 0 | 0 | 0 | 1 | 1 | 1 |
| 0 | 1 | 0 | 1 | 1 | 1 |
| 1 | 0 | 0 | 0 | 1 | 0 |
| 1 | 1 | 0 | 1 | 1 | 1 |
| 0 | 0 | 1 | 1 | 0 | 1 |
| 0 | 1 | 1 | 1 | 1 | 1 |
| 1 | 0 | 1 | 1 | 0 | 0 |
| 1 | 1 | 1 | 1 | 1 | 1 |

| $A$ | $B$ | $C$ | $A \rightarrow B \lor C$ | $\neg B \rightarrow \neg C$ | $A \rightarrow B$ |
|:---:|:---:|:---:|:---:|:---:|:---:|
| 0 | 0 | 0 | 1 | 1 | 1 |
| 0 | 1 | 0 | 1 | 1 | 1 |
| 1 | 1 | 0 | 1 | 1 | 1 |
| 0 | 1 | 1 | 1 | 1 | 1 |
| 1 | 1 | 1 | 1 | 1 | 1 |

$\therefore \{A\rightarrow B \lor C, \neg B\rightarrow \neg C\} \vDash A\rightarrow B$

### Exercise 5
2: $(\neg A \rightarrow \neg B)\rightarrow (A \rightarrow B) = 0$ when $A = 1, B = 0$  
3: $((P \land Q) \rightarrow R) \rightarrow (R \lor \neg P) = 0$ when $P=1, Q=0, R=0$