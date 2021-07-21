### Exercise 1
We wish to show that $f$ is injective, that is $f(x_1) = f(x_2) \implies x_1 = x_2$. Recall that, as $g \circ f$ is injective, it has a left inverse, call this function $h$. Now suppose that $f(x_1) = f(x_2)$. Then
$$
    \begin{align*}
        f(x_1) &= f(x_2) \\
        g(f(x_1)) &= g(f(x_2)) \\
        h(g(f(x_1))) &= h(g(f(x_2))) \\
        x_1 &= x_2
    \end{align*}
$$
And so, $f$ is injective, as required.

---

Suppose $f$ is the function $f(x) = 2*x$, which is trivially injective, and $g$ is the function where $g(x) = x$ when $x$ is even, otherwise $g(x) = x + 1$, which is trivially not injective. Then the resulting function $g \circ f$ is injective as all $f(x)$ are even, so $g(f(x)) = f(x)$ for all x, and $f$ itself is injective.

---

We wish to show that $g$ is injective. Recall that, as $g \circ f$ is injective, it has a left inverse, call this function $h$. Now suppose $g(y_1) = f(y_2)$. As $y_1, y_2 \in Y$, we have $x_1, x_2 \in X$ such that $f(x_1) = y_1$ and $f(x_2) = y_2$, by the surjectivity of $f$. Then
$$
    \begin{align*}
        g(y_1) &= g(y_2) \\
        g(f(x_1)) &= g(f(x_2)) \\
        h(g(f(x_1))) &= h(g(f(x_2))) \\
        x_1 &= x_2 \\
        f(x_1) &= f(x_2) \\
        y_1 &= y_2\\
    \end{align*}
$$
And so, $g$ is injective, as required.

### Exercise 2
Suppose $X = Y = \Z, Z = \{0\}$, $f$ is the function $f(x) = 2*x$, which is trivially not surjective, and $g$ is the function where $g(x) = 0$ which is surjective on $Z$. Then the resulting function $g \circ f$ is surjective as all $x$ get mapped to $0$.

---

We wish to show that $g$ is surjective, that is $\forall z, \exists y, g(y)=z$. Recall that, as $g \circ f$ is surjective, it has a right inverse, call this function $h$. Now let $z \in Z$, it suffices to find $y \in Y$ such that $g(y) = z$. We propose that $y = f(h(z))$ satisfies $g(y) = z$. Verifying
$$
    \begin{align*}
    g(y) &= g(f(h(z))) \\
    g(y) &= (g \circ f)(h(z)) \\
    g(y) &= z
    \end{align*}
$$
Therefore, $g$ is surjective, as required.

### Exercise 3
Let $x_1, x_2 \in \R$ and suppose that $f(x_1) = f(x_2)$. We wish to show that $x_1 = x_2$. Suppose $x_1 \neq x_2$, then either $x_1 < x_2$ or $x_1 > x_2$. It follows then that $f(x_1) < f(x_2)$ or $f(x_1) > f(x_2)$ as $f$ is strictly increasing. In either case we have that $f(x_1) \neq f(x_2)$, but this contradicts the premise, therefore $x_1 = x_2$. So we can conclude that $f$ is injective, as required.

---

Let $x_1, x_2 \in \R$, we wish to show $x_1 < x_2 \implies g(x_1) < g(x_2)$. It suffices to show the contrapositive $g(x_1) \geq g(x_2) \implies x_1 \geq x_2$. We proceed by cases, suppose $g(x_1) > g(x_2)$, then $f(g(x_1)) > f(g(x_2))$, as $f$ is strictly increasing. But $g$ is a right inverse to $f$ and so $x_1 > x_2 \implies x_1 \geq x_2$. Now suppose $g(x_1) = g(x_2)$, then $f(g(x_1)) = f(g(x_2))$. Again $g$ is a right inverse to $f$ and so $x_1 = x_2 \implies x_1 \geq x_2$. Therefore $g$ is strictly increasing, as required.

### Exercise 4
First suppose $y \in f[A \cup B]$, we wish to show $y \in f[A] \cup f[B]$. As $y \in f[A \cup B]$ we have some $x \in A \cup B$ such that $f(x) = y$. It follows then that $x \in A$ or $x \in B$, and so $y \in f[A]$ or $y \in f[B]$. Therefore $y \in f[A] \cup f[B]$, as required.

Now suppose that $y \in f[A] \cup f[B]$, we wish to show $y \in f[A \cup B]$. Then we have either $y \in f[A]$ or $y \in f[B]$. In the first case we have $x \in A$ such that $f(x) = y$, and in the second $x \in B$ such that $f(x) = y$. In either case we have $x \in A \cup B$, and so $y \in f[A \cup B]$, as required.

Therefore, $y \in f[A \cup B] = y \in f[A] \cup f[B]$.

### Exercise 5
Suppose that $y \in f[A]\backslash f[B]$, we wish to show $y \in f[A \backslash B]$. $y \in f[A]\backslash f[B]$ implies that there is $y \in f[A]$ and $y \notin f[B]$, and so there exists $x \in A$ such that $f(x) = y$ and no such $x$ in $B$. In particular this means that $x \notin B$ and so $x \in A \backslash B$. Therefore $y \in f[A \backslash B]$, and so $f[A]\backslash f[B] \subseteq f[A \backslash B]$.