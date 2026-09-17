왜냐하면 **형식체계에서는 자연어로 숨겨져 있는 조건을 전부 명시해야 하기 때문**입니다. 처음 보면 기호가 엄청 많아 보이지만, 사실 반복해서 나오는 몇 개만 알면 됩니다.

예를 들어 제가 쓴

$$
\Gamma \vdash t : A
$$

부터 보면 그냥 **“환경 Γ에서 프로그램 `t`의 타입은 `A`다”**라는 뜻입니다.

여기서 `Γ`(감마)는 지금까지 알고 있는 변수들의 목록입니다. 예를 들어 코드로 치면 대충

```text
x : Nat
y : Vec Nat x
```

같은 상태가 `Γ`입니다.

`⊢`는 특별한 연산이 아니라 **“이 조건 아래에서 다음을 판단할 수 있다”** 정도의 구분자입니다. 따라서

$$
\Gamma \vdash x : Nat
$$

은 그냥

> 현재 변수 환경 Γ에서 `x`는 `Nat` 타입이다.

입니다.

그리고 제가 쓴

$$
\Gamma\vdash t\Rightarrow A
$$

의 `⇒`는 **t만 보고 타입 A를 알아낸다(infer)**는 뜻이고,

$$
\Gamma\vdash t\Leftarrow A
$$

의 `⇐`는 **A라는 타입을 알려줬을 때 t가 정말 A인지 검사한다(check)**는 뜻입니다.

이건 실제 코드의 `infer()`와 `check()`를 수학 기호로 쓴 것뿐이에요.

---

분수처럼 생긴 것도 겁먹을 필요 없습니다.

예를 들어

$$
\frac{
\Gamma\vdash f:\Pi(x:A).B
\qquad
\Gamma\vdash a:A
}{
\Gamma\vdash f\,a:B[a/x]
}
$$

이걸 자연어로 읽으면:

> `f`가 A를 받는 함수이고,
> `a`가 A 타입이면,
> `f(a)`를 사용할 수 있다.

그게 전부입니다.

위쪽은 **필요조건**, 아래쪽은 **그 조건들이 만족되면 내릴 수 있는 결론**입니다.

프로그래밍스럽게 쓰면 오히려 익숙합니다.

```rust
if type_of(f) == Function(A, B)
    && type_of(a) == A
{
    type_of(apply(f, a)) = B_with_a_substituted;
}
```

수학자는 이걸 압축해서 분수 모양으로 쓰는 겁니다.

---

`Π`, `Σ`도 이름 때문에 어려워 보이는 겁니다.

`Π`는 **dependent function**입니다.

$$
\Pi(x:A).B(x)
$$

쉽게 쓰면

```text
(x: A) -> B(x)
```

입니다.

보통 함수

```text
Nat -> Bool
```

은 결과 타입 `Bool`이 입력과 상관없죠.

dependent function은

```text
(n: Nat) -> Vec String n
```

처럼 **입력값 `n`에 따라 결과의 타입 자체가 달라질 수 있습니다.**

`Σ`는 반대로 dependent pair입니다.

$$
\Sigma(n:Nat).Vec\;String\;n
$$

은 대충

```text
(n, vector)
```

인데 `vector`의 길이가 반드시 앞에 들어 있는 `n`이어야 한다는 뜻입니다.

---

`≡`도 자주 나옵니다.

$$
t\equiv u
$$

는 이 커널에서 **계산해 보면 같은 것**이라는 뜻입니다.

예를 들어

$$
(\lambda x.x)\;3\equiv3
$$

입니다.

코드에서는 `nbe.rs`의 evaluation/conversion 부분이 이런 것을 판정합니다.

---

그리고 `∀`, `∃` 같은 논리 기호가 MLTT에서 함수/쌍과 연결되는 것도 기호가 많아지는 이유 중 하나입니다.

재미있게도

$$
\forall x:A.\;P(x)
$$

를 type theory에서는

$$
\Pi(x:A).P(x)
$$

로 볼 수 있고,

$$
\exists x:A.\;P(x)
$$

는

$$
\Sigma(x:A).P(x)
$$

와 대응시킬 수 있습니다.

즉 **프로그램의 타입을 설명하는 언어가 동시에 논리를 설명하는 언어**가 됩니다.

그래서 dependent type theory를 처음 보면 갑자기 그리스 문자와 논리 기호가 폭발합니다.

하지만 이 저장소를 읽는 데 당장 필요한 건 사실 이것 정도입니다:

| 기호                | 그냥 이렇게 읽으면 됨    |
| ----------------- | --------------- |
| `Γ`               | 현재 변수/타입 환경     |
| `Γ ⊢ ...`         | Γ에서 ...라고 판단 가능 |
| `t : A`           | t의 타입은 A        |
| `⇒ A`             | 타입 A를 추론        |
| `⇐ A`             | 타입 A인지 검사       |
| `Π(x:A).B`        | `(x: A) -> B`   |
| `Σ(x:A).B`        | dependent pair  |
| `Type₀, Type₁...` | 타입들의 단계         |
| `t ≡ u`           | 계산상 같은 항        |
| `B[a/x]`          | B 안의 x를 a로 바꿈   |

그러니까 아까 제가 적은

$$
\frac{
\Gamma\vdash f\Rightarrow\Pi(x:A).B
\qquad
\Gamma\vdash a\Leftarrow A
}{
\Gamma\vdash f\,a\Rightarrow B[a/x]
}
$$

도 이제는 그냥:

> **“f가 A를 받는 함수라고 추론되고, a가 A인지 검사해서 통과하면, `f a`의 타입은 결과 타입 B에서 x를 실제 인자 a로 바꾼 것이다.”**

라는 뜻입니다.

이 정도 기호만 익히고 `check.rs`를 다시 보면, 오히려 **Rust 코드 수십 줄이 수식 한 줄을 구현하고 있다는 것**이 보이기 시작합니다.
