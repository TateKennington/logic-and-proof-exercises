### Exercise 1
To show $A \cup (B \cap C) = (A \cup B)\cap(A \cup C)$ it suffices to show that $x \in A \cup (B \cap C) \iff x \in (A \cup B)\cap(A \cup C)$.

First assume that $x \in A \cup (B \cap C)$ , then there are two cases $x \in A$ or $x \in B \cap C$. If $x \in A$ then, $x \in A \cup B$ and $x \in A \cup C$, so $x \in (A \cup B)\cap(A \cup C)$ by definition. Otherwise if $x \in B \cap C$, then $x \in B$ and $x \in C$, so $x \in A \cup B$ and $x \in A \cup C$, and therefore $x \in (A \cup B)\cap(A \cup C)$. Thus we have that $x \in A \cup (B \cap C) \implies x \in (A \cup B)\cap(A \cup C)$.

Next assume that $x \in (A \cup B)\cap(A \cup C)$. This means that $x \in A \cup B$ and $x \in A \cup B$. Consider the case where $x \in A$. Then trivially $x \in A \cup (B \cap C)$. Next consider the case where $x \notin A$. As we have $x \in A \cup B$ and $x \in A \cup B$ it follows then that $x \in B$ and $x \in C$. Therefore $x \in B \cap C$, and so $x \in A \cup (B \cap C)$. So we can conclude that $x \in (A \cup B)\cap(A \cup C) \implies x \in A \cup (B \cap C)$.

Applying these two results we have that $x \in A \cup (B \cap C) \iff x \in (A \cup B)\cap(A \cup C)$, and so $A \cup (B \cap C) = (A \cup B)\cap(A \cup C)$, as required.

### Exercise 2
$$
    \begin{align*}
    x \in \overline{A \backslash B} &\iff x \in \overline{A \cap \bar B}\\
    &\iff x \in \bar A \cup B
    \end{align*}
$$

### Exercise 3
Suppose there exists $x$ such that $x \in C, D$. Then we have that $x \in A, B$ as $C \sube A$ and $D \sube B$. However, this is a contradiction, as $A$ and $B$ are disjoint. Therefore such an $x$ does not exist, and $C$ and $D$ are disjoint.

### Exercise 4
$$
    \begin{align*}
    (A \cup B) \backslash (A \cap B) &= \{x|(x \in A \lor x \in B) \land \neg(x \in A \land x \in B)\}\\
    &= \{x|(x \in A \lor x \in B) \land (x \notin A \lor x \notin B)\}\\
    &= \{x | (x \in A \land x \notin A) \lor (x \in A \land x \notin B) \lor (x \in B \land x \notin A)\} \lor (x \in B \land x \notin B)\}\\
    &= \{x | (x \in A \land x \notin B) \lor (x \in B \land x \notin A)\}\\
    &= (A \backslash B) \cup (B \backslash A)
    \end{align*}
$$

### Exercise 5
$$
    \begin{align*}
    A \backslash(B \cup C) &= A \cap \overline{(B \cup C)} \\
    &= A \cap \bar B \cap \bar C\\
    &=(A \backslash B) \cap \bar C\\
    &=(A \backslash B) \backslash C
    \end{align*}
$$

### Exercise 6
$$
    \begin{align*}
    (A \backslash B) \cup (A \cap B) &= (A \cap \bar B) \cup (A \cap B)\\
    &=A\cap(B \cup \bar B)\\
    &=A
    \end{align*}
$$

### Exercise 7
$$
    \begin{align*}
    A \backslash B &= A \backslash B \cup \empty\\
    &= (A \cap \bar B) \cup (A \cap \bar A)\\
    &= A \cap (\bar A \cup \bar B)\\
    &= A \cap \overline{(A \cup B)}\\
    &= A \backslash (A \cup B)
    \end{align*}
$$

$$
    \begin{align*}
    A \backslash B &= A \backslash B \cup \empty\\
    &= (A \cap \bar B) \cup (B \cap \bar B)\\
    &= (A \cup B) \cap \bar B\\
    &= (A \cup B) \backslash B
    \end{align*}
$$

$$
    \begin{align*}
    (A \cap B) \backslash C &= (A \cap B) \cap \bar C \\
    &= (A \cap \bar C) \cap B \\
    &= (A \backslash C) \cap B
    \end{align*}
$$

### Exercise 8
Let $x \in \bigcup_{i\in I}\bigcap_{j\in J}A_{i,j}$. Then by definition $\exists i, \forall j, x \in A_{i, j}$. Therefore $\forall j, \exists i, x \in A_{i, j}$ and so $x \in \bigcap_{j\in J}\bigcup_{i\in I}A_{i,j}$. This means that $\bigcup_{i\in I}\bigcap_{j\in J}A_{i,j} \sube \bigcap_{j\in J}\bigcup_{i\in I}A_{i,j}$.

However, the reverse inclusion is not true in general. Consider $A_{i,j} = \{0\}$ when $i = j$ and $A_{i, j} = \empty$ otherwise. Then $\bigcap_{j\in J}\bigcup_{i\in I}A_{i,j} = \{0\}$ whereas $\bigcup_{i\in I}\bigcap_{j\in J}A_{i,j} = \empty$, so $\bigcap_{j\in J}\bigcup_{i\in I}A_{i,j} \nsubseteq \bigcup_{i\in I}\bigcap_{j\in J}A_{i,j}$

### Exercise 9
$$
    \begin{align*}
    (\bigcup_{i\in I} A_i) \cap (\bigcup_{j\in J} B_j) &= \bigcup_{i\in I} (A_i \cap (\bigcup_{j\in J} B_j))\\
    &=\bigcup_{i\in I,j\in J} (A_i \cap B_j)
    \end{align*}
$$

### Exercise 10
The reverse implication follows trivially from the definition of equality, so it remains to show that $(a, b, c) = (d, e, f) \implies a = d, b = e, c = f$. Expanding the definition of an ordered triple we have $(a, (b, c)) = (d, (e, f))$. This implies that $a = d$ and $(b, c) = (e, f)$, from equality of ordered pairs$. Applying the definition of equality again we have $b = e, c = f$. Therefore we have that $(a, b, c) = (d, e, f) \implies a = d, b = e, c = f$ and so $(a, b, c) = (d, e, f)$ if and only if $a = d, b = e, c = f$.

### Exercise 11
First we show that $A \times (B \cup C) \sube (A \times B) \cup (A \times C)$. Let $(x, y) \in A \times (B \cup C)$, then $x \in A$ and $y \in B$ or $y \in C$. If $y \in B$ then $(x, y) \in A \times B$, and so $(x, y) \in (A \times B) \cup (A \times C)$. Likewise if $y \in C$ then $(x, y) \in A \times C$, and so $(x, y) \in (A \times B) \cup (A \times C)$. Therefore, $A \times (B \cup C) \sube (A \times B) \cup (A \times C)$.

Next we show that $(A \times B) \cup (A \times C) \sube A \times (B \cup C)$. Let $(x, y) \in (A \times B) \cup (A \times C)$, then $x \in A$ and either $y \in B$ or $y \in C$. Therefore $y \in B \cup C$, and so $(x, y) \in A \times (B \cup C)$. Thus we can conclude that $(A \times B) \cup (A \times C) \sube A \times (B \cup C)$.

Applying both results we have $A \times (B \cup C) = (A \times B) \cup (A \times C)$

### Exercise 12
$$
    \begin{align*}
    (A \cap B) \times (C \cap D) &= \{(x, y)|x\in A \cap B \land y \in C \cap D\}\\
    &= \{(x, y)|x\in A \land x \in B \land y \in C \land y \in D\}\\
    &= \{(x, y)|(x\in A \land y \in C) \land (x \in B \land y \in D)\}\\
    &= \{(x, y)|(x, y) \in A \times C \land (x, y) \in B \times D\}\\
    &= (A \times C) \cap (B \times D)
    \end{align*}
$$

$$
    \begin{align*}
    (A \cup B) \times (C \cup D) &= \{(x, y)|x\in A \cup B \land y \in C \cup D\}\\
    &= \{(x, y)|(x\in A \lor x \in B) \land (y \in C \lor y \in D)\}\\
    &= \{(x, y)|(x\in A \land y \in C) \lor (x\in A \land y \in D) \lor (x\in B \land y \in C) \lor (x\in B \land y \in D)\}\\
    &= \{(x, y)|(x, y) \in A \times C \lor (x, y) \in A \times D \lor (x, y) \in B \times C \lor (x, y) \in B \times D\}\\
    &= (A \times C) \cup (A \times D) \cup (B \times C) \cup (B \times D)
    \end{align*}
$$

### Exercise 13
First suppose that $A \sube B$, now we want to show that $\mathcal{P}(A) \sube \mathcal{P}(B)$. Let $C \in \mathcal{P}(A)$, then $C \sube A$, and so $C \sube B$, by the transitive property. This means that $C \in \mathcal{P}(B)$, and therefore $\mathcal{P}(A) \sube \mathcal{P}(B)$.

Next suppose that $\mathcal{P}(A) \sube \mathcal{P}(B)$, we wish to show $A \sube B$. Recall that $A \sube A$, by reflexivity, and so $A \in \mathcal{P}(A)$. Therefore $A \in \mathcal{P}(B)$, $\mathcal{P}(A) \sube \mathcal{P}(B)$, and so $A \sube B$.

Thus we can conclude that $A \sube B$ if and only if $\mathcal{P}(A) \sube \mathcal{P}(B)$.