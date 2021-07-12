### Exercise 1
To show that $\leq$ is a partial order we must show that it is reflexive, transitive, and antisymmetric. Reflexitivity follows from the reflex property of equality as $a = a \implies a \leq a$. 

Next we show that $\leq$ is antisymmetric, that is $a \leq b \land b \leq a \implies a = b$, we do this by reasoning by cases. First consider the expression $a \leq b$, if $a = b$ we're done, so we consider the $a < b$ case. Next consider the expression $b \leq a$, again in the $b = a$ case we are done, so we consider the case where $b < a$. In this case it follows that $a < a$ from the transitive property, however this is a contradiction as $<$ is irreflexive, so this case is invalid. Therefore in all valid cases $a = b$, and so $\leq$ is antisymmetric.

Finally we show that $\leq$ is transitive, that is $a \leq b \land b \leq c \implies a \leq c$. Again we reason by cases. Suppose that $a = b$, then we have that $a \leq c$ buy substituting $b$ for $a$ in $b \leq c$. Likewise if $b = c$ then we have $a \leq c$ from substituting $b$ for $c$ in $a \leq b$. It therefore remains to show that $a \leq c$ in the case where $a < b$ and $b < c$. In this case we have $a < c$ by the transitive property, and so $a \leq c$, as required.

Now suppose that $<$ is a total order, we wish to show that $\leq$ is also total. As $<$ is total we have that $\forall ab,a<b \lor a = b \lor a>b$. Notice that, $a<b \implies a \leq b$, $a=b \implies a \leq b$, and $a > b \implies a \geq b$, by definition. So we have that $\forall ab,a \leq b \lor a \geq b$, therefore $\leq$ is also total.

### Exercise 2
First suppose that $a<b$, we want to show that $a \leq b \land a \neq b$. The fact that $a \leq b$ follows from the definition of $\leq$. Now suppose $a = b$, then by substitution we have $a < a$, however this is a contradiction, and so $a \neq b$.

Next suppose that $a \leq b \land a \neq b$ we want to show $a<b$. The fact that $a \leq b$ means that either $a < b$ or $a = b$, however $a \neq b$ from the premise, so it follows that $a < b$, as required.

Therefore $a<b \iff a \leq b \land a \neq b$.

### Exercise 3
On an arbitrary graph $\leq$ is none of the above.

Consider the graph $A \rightarrow B \rightarrow C$. On this graph transitivity fails, as $A \leq B \land B \leq C$ but $A \nleq C$, so $\leq$ is not a partial order or a strict partial order. Futhermore, totality fails because $A \nleq C$ and $A \ngeq C$, so $\leq$ is not total on this graph either.

### Exercise 4
First suppose that $[a] = [b]$, we wish to show $a \equiv b$. By the reflexive property we have $a \equiv a$ and so $a \in [a]$. Therefore $a \in [b]$ from the premise, and so $a \equiv b$.

Next suppose that $a \equiv b$, we wish to show $[a] = [b]$. Consider some element $c \in [a]$, then $c \equiv a$, by definition. Furthermore, from the transitive property $c \equiv b$, and so $c \in [b]$ and $[a] \sube [b]$. By the same logic we have $[b] \sube [a]$, and that $[a] = [b]$, as required.

Therefore $[a] = [b] \iff a \equiv b$.

### Exercise 5
To show that ~ is an equivalence relation we must show that it is reflexive, symmetric and transitive.

The reflexivity of ~ follows from the definition of ~.

Next we show symmetry. Suppose $a \text{\textasciitilde} b$. The either $a = b$, $b = a + 1$, or $b = a - 1$. If $a = b$, then trivially $b \text{\textasciitilde} a$. If $b = a - 1$ then $a$ is odd and $b$ is even, so $b \text{\textasciitilde} b + 1 \implies b \text{\textasciitilde} a - 1 + 1 \implies b \text{\textasciitilde} a$. Likewise if $b = a + 1$ then $a$ is even and $b$ is odd, so $b \text{\textasciitilde} b - 1 \implies b \text{\textasciitilde} a + 1 - 1 \implies b \text{\textasciitilde} a$. Therefore ~ is symmetric.

Finally we show transitivity. Suppose $a \text{\textasciitilde} b$ and $b \text{\textasciitilde} c$. In the case where $a = b$ or $b = c$, the conclusion follows from substitution. Now we consider the remaining case. First suppose that $a$ is odd, then $b = a - 1$ and is even, so $c = b + 1 = a$, so $a \text{\textasciitilde} c$. Now suppose that $a$ is even, then $b = a + 1$ and is odd, so $c = b - 1 = a$, so again $a \text{\textasciitilde} c$. Therefore ~ is transitive.

Thus we can conclude that ~ is an equivalence relation.

$[5] = \{4, 5\}$

The set of equivalences classes contains all sets of the form $\{2n, 2n+1\},n\in \N$.

### Exercise 6
To show that the relation is an equivalence relation we must show that it is reflexive, symmetric and transitive. Recall the fact that two lines are parallel if and only if they have the same gradient. Therefore reflexivity, symmetry, and transitivity each follow from the same property of equality on $\R$.

The equivalence class of the x-axis is the set of all horizontal lines, that is lines with 0 gradient.

The set of all equivalences contains all sets of lines with a fixed gradient.

### Exercise 7
To show that $\equiv$ is an equivalence relation we must show that it is reflexive, symmetric and transitive.

First we show reflexivity. We have $a \leq a$ from the reflexivity of $\leq$, so in particular $a \leq a \land a \leq a$ is true. Therefore $a \equiv a$ by definition.

Next we show symmetry. Suppose $a \equiv b$, then $a \leq b$ and $b \leq a$, so $b \equiv a$ by definition.

It remains to show that $\equiv$ is transitive. Suppose that $a \equiv b$ and $b \equiv c$. Expanding definitions we have $a \leq b$, $b \leq a$, $b \leq c$, and $c \leq b$. Applying the transitivity of $\leq$ yields $a \leq c$ and $c \leq a$, so $a \equiv c$ as required.

Therefore $\equiv$ is an equivalence relation.