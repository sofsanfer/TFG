(*<*) 
theory Hintikka
  imports 
    Sintaxis
    Semantica
begin
(*>*)

section \<open>Conjuntos de Hintikka y propiedades básicas\<close>

text \<open>En esta sección presentaremos un tipo de conjuntos de fórmulas:
  los conjuntos de Hintikka. Probaremos finalmente que todo conjunto 
  de Hintikka es satisfacible.

  \begin{definicion}
  Se llama \<open>conjunto de Hintikka\<close> a todo conjunto de fórmulas \<open>S\<close> que
  verifica las siguientes condiciones:
    \begin{enumerate}
      \item \<open>\<bottom>\<close> no pertenece a \<open>S\<close>.
      \item Dada \<open>p\<close> una fórmula atómica cualquiera, \<open>p\<close> y \<open>\<not> p\<close> no 
        pertenecen simultáneamente a \<open>S\<close>.
      \item Si \<open>F \<and> G\<close> pertenece a \<open>S\<close>, entonces \<open>F\<close> y \<open>G\<close> 
        pertenecen a \<open>S\<close>.
      \item Si \<open>F \<or> G\<close> pertenece a \<open>S\<close>, entonces \<open>F\<close> pertenece a
        \<open>S\<close> o \<open>G\<close> pertenece a \<open>S\<close>.
      \item Si \<open>F \<rightarrow> G\<close> pertenece a \<open>S\<close>, entonces \<open>\<not> F\<close> pertenece 
        a \<open>S\<close> o \<open>G\<close> pertenece a \<open>S\<close>.
      \item Si \<open>\<not>(\<not> F)\<close> pertenece a \<open>S\<close>, entonces \<open>F\<close> pertenece 
        a \<open>S\<close>.
      \item Si \<open>\<not>(F \<and> G)\<close> pertenece a \<open>S\<close>, entonces \<open>\<not> F\<close> 
        pertenece a \<open>S\<close> o \<open>\<not> G\<close> pertenece a \<open>S\<close>.
      \item Si \<open>\<not>(F \<or> G)\<close> pertenece a \<open>S\<close>, entonces \<open>\<not> F\<close> y \<open>\<not> G\<close> 
        pertenecen a \<open>S\<close>.
      \item Si \<open>\<not>(F \<rightarrow> G)\<close> pertenece a \<open>S\<close>, entonces \<open>F\<close> y \<open>\<not> G\<close> 
        pertenecen a \<open>S\<close>.
    \end{enumerate}  
  \end{definicion}

  En Isabelle se formaliza mediante el tipo \<open>definition\<close> de la siguiente
  manera.\<close>

definition "Hintikka S \<equiv> 
(\<bottom> \<notin> S
  \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
  \<and> (\<forall>F G. F \<^bold>\<and> G \<in> S \<longrightarrow> F \<in> S \<and> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<or> G \<in> S \<longrightarrow> F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> \<^bold>\<not>F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S))"

text \<open>A continuación ilustramos con un ejemplo de conjunto de fórmulas
  de Hintikka.\<close>

notepad
begin

  have "Hintikka {Atom 0 \<^bold>\<and> ((\<^bold>\<not> (Atom 1)) \<^bold>\<rightarrow> Atom 2), 
                 ((\<^bold>\<not> (Atom 1)) \<^bold>\<rightarrow> Atom 2), 
                 Atom 0, \<^bold>\<not>(\<^bold>\<not> (Atom 1)), Atom 1}"
    unfolding Hintikka_def by simp

end

text \<open>En contraposición, el siguiente conjunto de fórmulas no es
  de Hintikka, pues no cumple la segunda condición de la definición 
  anterior.\<close>

notepad
begin

  have "\<not> Hintikka {Atom 0 \<^bold>\<and> ((\<^bold>\<not> (Atom 1)) \<^bold>\<rightarrow> Atom 2), 
                 ((\<^bold>\<not> (Atom 1)) \<^bold>\<rightarrow> Atom 2), 
                 Atom 0, \<^bold>\<not>(\<^bold>\<not> (Atom 1)), Atom 1, \<^bold>\<not>(Atom 1)}"
    unfolding Hintikka_def by auto

end

text \<open>En adelante presentaremos una serie de lemas auxiliares
  derivados de la definición de conjunto de Hintikka que nos facilitarán
  posteriormente las demostraciones en Isabelle/HOL.

  El primer lema expresa que la conjunción de las nueve condiciones de 
  la definición anterior es una condición necesaria para que un conjunto 
  sea de Hintikka.\<close>

lemma auxEq: 
  assumes "Hintikka S"
  shows "\<bottom> \<notin> S
  \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
  \<and> (\<forall>F G. F \<^bold>\<and> G \<in> S \<longrightarrow> F \<in> S \<and> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<or> G \<in> S \<longrightarrow> F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> \<^bold>\<not>F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S)"
proof -
  have "Hintikka S = ( \<bottom> \<notin> S
  \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
  \<and> (\<forall>F G. F \<^bold>\<and> G \<in> S \<longrightarrow> F \<in> S \<and> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<or> G \<in> S \<longrightarrow> F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> \<^bold>\<not>F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S))" 
    using Hintikka_def by (simp only: atomize_eq)
  then show ?thesis
    using assms by (rule iffD1)
qed

text \<open>Asimismo presentaremos nueve lemas correspondientes a cada
  condición de la definición de conjunto de Hintikka. 

  \begin{lema}
    Si \<open>S\<close> es un conjunto de Hintikka, \<open>\<bottom>\<close> no pertenece a \<open>S\<close>.
  \end{lema}

  \begin{lema}
    Si \<open>p\<close> es una fórmula atómica que pertenece a un conjunto de 
    Hintikka \<open>S\<close>, entonces \<open>\<not> p\<close> no pertenece a \<open>S\<close>.
  \end{lema}

  \begin{lema}
    Si \<open>F \<and> G\<close> pertenece a un conjunto de Hintikka \<open>S\<close>, entonces \<open>F\<close> y 
    \<open>G\<close> pertenecen a \<open>S\<close>.
  \end{lema}

  \begin{lema}
    Si \<open>F \<or> G\<close> pertenece a un conjunto de Hintikka \<open>S\<close>, entonces \<open>F\<close> 
    pertenece a \<open>S\<close> o \<open>G\<close> pertenece a \<open>S\<close>.
  \end{lema}

  \begin{lema}
    Si \<open>F \<rightarrow> G\<close> pertenece a un conjunto de Hintikka \<open>S\<close>, entonces \<open>\<not> F\<close> 
    pertenece a \<open>S\<close> o \<open>G\<close> pertenece a \<open>S\<close>.
  \end{lema}

  \begin{lema}
    Si \<open>\<not>(\<not> F)\<close> pertenece a un conjunto de Hintikka \<open>S\<close>, entonces \<open>F\<close> 
    pertenece a \<open>S\<close>.
  \end{lema}

  \begin{lema}
    Si \<open>\<not>(F \<and> G)\<close> pertenece a un conjunto de Hintikka \<open>S\<close>, entonces 
    \<open>\<not> F\<close> pertenece a \<open>S\<close> o \<open>\<not> G\<close> pertenece a \<open>S\<close>.
  \end{lema}

  \begin{lema}
    Si \<open>\<not>(F \<or> G)\<close> pertenece a un conjunto de Hintikka \<open>S\<close>, entonces 
    \<open>\<not> F\<close> y \<open>\<not> G\<close> pertenecen a \<open>S\<close>.
  \end{lema}

  \begin{lema}
    Si \<open>\<not>(F \<rightarrow> G)\<close> pertenece a un conjunto de Hintikka \<open>S\<close>, entonces \<open>F\<close> 
    y \<open>\<not> G\<close> pertenecen a \<open>S\<close>.
  \end{lema}

  Como se puede observar, los lemas anteriores se corresponden con 
  cada condición necesaria de la definición de conjunto de Hintikka. 
  De este modo, la prueba de estos resultados se obtiene directamente 
  de dicha definición al suponer que \<open>S\<close> es un conjunto de Hintikka.

  Su formalización y demostración en Isabelle/HOL son las siguientes.\<close>

lemma
  assumes "Hintikka S" 
  shows "\<bottom> \<notin> S"
proof -
 have "\<bottom> \<notin> S
  \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
  \<and> (\<forall>F G. F \<^bold>\<and> G \<in> S \<longrightarrow> F \<in> S \<and> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<or> G \<in> S \<longrightarrow> F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> \<^bold>\<not>F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S)"
    using assms by (rule auxEq)
  thus "\<bottom> \<notin> S" by (rule conjunct1)
qed

lemma Hintikka_l1: 
 "Hintikka S \<Longrightarrow> \<bottom> \<notin> S"
  using Hintikka_def by blast

lemma
  assumes "Hintikka S" 
  shows "Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<notin> S"
proof (rule impI)
  assume H:"Atom k \<in> S"
 have "\<bottom> \<notin> S
  \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
  \<and> (\<forall>F G. F \<^bold>\<and> G \<in> S \<longrightarrow> F \<in> S \<and> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<or> G \<in> S \<longrightarrow> F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> \<^bold>\<not>F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S)"
   using assms by (rule auxEq)
  then have "(\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)"
    by (iprover elim: conjunct2 conjunct1)
  then have "\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<notin> S"
    by (simp only: not_def)
  then have "Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<notin> S"
    by (rule allE)
  thus "\<^bold>\<not> (Atom k) \<notin> S"
    using H by (rule mp)
qed

lemma Hintikka_l2: 
 "Hintikka S \<Longrightarrow>  (Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<notin> S)"
  by (smt Hintikka_def)

lemma 
  assumes "Hintikka S"
  shows "F \<^bold>\<and> G \<in> S \<longrightarrow> F \<in> S \<and> G \<in> S"
proof (rule impI)
  assume "F \<^bold>\<and> G \<in> S"
 have "\<bottom> \<notin> S
  \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
  \<and> (\<forall>F G. F \<^bold>\<and> G \<in> S \<longrightarrow> F \<in> S \<and> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<or> G \<in> S \<longrightarrow> F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> \<^bold>\<not>F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S)"
   using assms by (rule auxEq)
  then have "\<forall>F G. F \<^bold>\<and> G \<in> S \<longrightarrow> F \<in> S \<and> G \<in> S"
    by (iprover elim: conjunct2 conjunct1) 
  then have "F \<^bold>\<and> G \<in> S \<longrightarrow> F \<in> S \<and> G \<in> S"
    by (iprover elim: allE)
  thus "F \<in> S \<and> G \<in> S"
    using \<open>F \<^bold>\<and> G \<in> S\<close> by (rule mp)
qed

lemma Hintikka_l3: 
 "Hintikka S \<Longrightarrow>  (F \<^bold>\<and> G \<in> S \<longrightarrow> F \<in> S \<and> G \<in> S)"
  by (smt Hintikka_def)

lemma
  assumes "Hintikka S"
  shows "F \<^bold>\<or> G \<in> S \<longrightarrow> F \<in> S \<or> G \<in> S"
proof (rule impI)
  assume H:"F \<^bold>\<or> G \<in> S"
 have "\<bottom> \<notin> S
  \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
  \<and> (\<forall>F G. F \<^bold>\<and> G \<in> S \<longrightarrow> F \<in> S \<and> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<or> G \<in> S \<longrightarrow> F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> \<^bold>\<not>F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S)"
   using assms by (rule auxEq)
  then have "\<forall>F G. F \<^bold>\<or> G \<in> S \<longrightarrow> F \<in> S \<or> G \<in> S" 
    by (iprover elim: conjunct2 conjunct1)
  then have "F \<^bold>\<or> G \<in> S \<longrightarrow> F \<in> S \<or> G \<in> S"
    by (iprover elim: allE)
    thus "F \<in> S \<or> G \<in> S"
      using H by (rule mp)
  qed

lemma Hintikka_l4: 
 "Hintikka S \<Longrightarrow>  (F \<^bold>\<or> G \<in> S \<longrightarrow> F \<in> S \<or> G \<in> S)"
  by (smt Hintikka_def)

lemma
  assumes "Hintikka S" 
  shows "F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> \<^bold>\<not>F \<in> S \<or> G \<in> S"
proof (rule impI)
  assume H:"F \<^bold>\<rightarrow> G \<in> S"
 have "\<bottom> \<notin> S
  \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
  \<and> (\<forall>F G. F \<^bold>\<and> G \<in> S \<longrightarrow> F \<in> S \<and> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<or> G \<in> S \<longrightarrow> F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> \<^bold>\<not>F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S)"
   using assms by (rule auxEq)
  then have "\<forall>F G. F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> \<^bold>\<not>F \<in> S \<or> G \<in> S"
    by (iprover elim: conjunct2 conjunct1)
  then have "F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> \<^bold>\<not>F \<in> S \<or> G \<in> S"
    by (iprover elim: allE)
  thus "\<^bold>\<not>F \<in> S \<or> G \<in> S"
    using H by (rule mp)
qed

lemma Hintikka_l5: 
 "Hintikka S \<Longrightarrow>   (F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> \<^bold>\<not>F \<in> S \<or> G \<in> S)"
  by (smt Hintikka_def)

lemma
  assumes "Hintikka S"
  shows "(\<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<in> S)"
proof (rule impI)
  assume H:"\<^bold>\<not> (\<^bold>\<not>F) \<in> S"
 have "\<bottom> \<notin> S
  \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
  \<and> (\<forall>F G. F \<^bold>\<and> G \<in> S \<longrightarrow> F \<in> S \<and> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<or> G \<in> S \<longrightarrow> F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> \<^bold>\<not>F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S)"
   using assms by (rule auxEq)
  then have "\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<in> S"
    by (iprover elim: conjunct2 conjunct1)
  then have "\<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<in> S"
    by (rule allE)
  thus "F \<in> S"
    using H by (rule mp)
qed

lemma Hintikka_l6: 
 "Hintikka S \<Longrightarrow> \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<in> S"
  by (smt Hintikka_def)

lemma 
  assumes "Hintikka S" 
  shows "\<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S"
proof (rule impI)
  assume H:"\<^bold>\<not>(F \<^bold>\<and> G) \<in> S"
 have "\<bottom> \<notin> S
  \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
  \<and> (\<forall>F G. F \<^bold>\<and> G \<in> S \<longrightarrow> F \<in> S \<and> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<or> G \<in> S \<longrightarrow> F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> \<^bold>\<not>F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S)"
   using assms by (rule auxEq)
  then have "\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S"
    by (iprover elim: conjunct2 conjunct1)
  then have "\<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S"
    by (iprover elim: allE)
    thus "\<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S"
      using H by (rule mp)
  qed

lemma Hintikka_l7: 
 "Hintikka S \<Longrightarrow> \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S"
  by (smt Hintikka_def)

lemma
  assumes "Hintikka S" 
  shows "\<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S"
proof (rule impI)
  assume H:"\<^bold>\<not>(F \<^bold>\<or> G) \<in> S"
 have "\<bottom> \<notin> S
  \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
  \<and> (\<forall>F G. F \<^bold>\<and> G \<in> S \<longrightarrow> F \<in> S \<and> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<or> G \<in> S \<longrightarrow> F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> \<^bold>\<not>F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S)"
   using assms by (rule auxEq)
  then have "\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S"
    by (iprover elim: conjunct2 conjunct1)
  then have "\<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S"
    by (iprover elim: allE)
  thus "\<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S"
    using H by (rule mp)
qed

lemma Hintikka_l8: 
 "Hintikka S \<Longrightarrow> ( \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S)"
  by (smt Hintikka_def)

lemma 
  assumes "Hintikka S" 
  shows "\<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S"
proof (rule impI)
  assume H:"\<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S"
 have "\<bottom> \<notin> S
  \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
  \<and> (\<forall>F G. F \<^bold>\<and> G \<in> S \<longrightarrow> F \<in> S \<and> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<or> G \<in> S \<longrightarrow> F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> \<^bold>\<not>F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S)"
   using assms by (rule auxEq)
  then have "\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S"
    by (iprover elim: conjunct2)
  then have "\<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S"
    by (iprover elim: allE)
  thus "F \<in> S \<and> \<^bold>\<not> G \<in> S"
    using H by (rule mp)
qed

lemma Hintikka_l9: 
 "Hintikka S \<Longrightarrow> \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S"
  by (smt Hintikka_def)

text \<open>Las pruebas anteriores siguen un esquema similar en Isabelle. 
  En primer lugar, mediante el lema \<open>auxEq\<close>, al suponer inicialmente
  que el conjunto es de Hintikka, se verifica la conjunción de las 
  condiciones de su definición. Posteriormente se emplean distintos
  métodos para disgregar estas condiciones en los distintos lemas. Para 
  este propósito se utiliza, en particular, la táctica de 
  demostración \<open>(iprover elim: \<open>rules\<close>)\<close>. Con esta táctica aplicamos
  reiteradamente una o varias reglas y reducimos pasos en la prueba de\\ 
  Isabelle/HOL. Para ello, nos hemos servido del método de demostración 
  \<open>elim\<close> que permite aplicar repetidamente reglas de 
  eliminación especificadas. En nuestro caso, hemos utilizado las reglas 
  de eliminación de la conjunción y la regla de eliminación del 
  cuantificador existencial. Por otro lado, \<open>iprover\<close> es un 
  buscador intuitivo de métodos de demostración en Isabelle/HOL que 
  depende del contexto y de las reglas o métodos específicamente 
  declarados a continuación del mismo. De este modo, combinando ambos, 
  \<open>iprover\<close> busca intuitivamente el método de demostración que, mediante 
  la aplicación reiterada de reglas de eliminación señaladas por \<open>elim\<close>, 
  pruebe adecuadamente el resultado.

  Finalmente, veamos un resultado derivado de las condiciones
  exigidas a los conjuntos de Hintikka.

  \begin{lema}
    Dado un conjunto de Hintikka, una fórmula no pertenece al conjunto 
    si su negación sí pertenece al mismo. Es decir, si \<open>S\<close> es un 
    conjunto de Hintikka y \<open>\<not> F \<in> S\<close>, entonces \<open>F \<notin> S\<close>.
  \end{lema}

  Antes de pasar a la demostración del resultado, cabe añadir que
  para su prueba utilizaremos la regla lógica \<open>modus tollens\<close>. 

  \begin{lema}[Modus tollens]
   Si \<open>P\<close> implica \<open>Q\<close> y \<open>Q\<close> es falso, entonces \<open>P\<close> es también falso.
  \end{lema}

  Teniendo esto en cuenta, la demostración del lema es la siguiente.

\begin{demostracion}
    La prueba se realiza por inducción sobre la estructura de las 
    fórmulas proposicionales. Veamos los distintos casos.

    En primer lugar, consideremos una fórmula atómica cualquiera \<open>p\<close> y 
    \<open>S\<close> un conjunto de Hintikka. Supongamos que \<open>\<not> p \<in> S\<close>. 
    Por definición de conjunto de Hintikka, si \<open>p \<in> S\<close>, entonces 
    \<open>\<not> p \<notin> S\<close>, en contra de la hipótesis. Luego, aplicando la regla de 
    \<open>modus tollens\<close>, se tiene que \<open>p \<notin> S\<close>.

    Sea la fórmula \<open>\<bottom>\<close> y \<open>S\<close> un conjunto de Hintikka. Supongamos 
    que \<open>\<not> \<bottom> \<in> S\<close>. Como \<open>S\<close> es un conjunto de Hintikka, 
    verifica la primera condición de la definición: \<open>\<bottom> \<notin> S\<close>, como 
    queríamos demostrar.

    Consideremos \<open>S\<close> un conjunto de Hintikka. Sea \<open>F\<close> una fórmula
    cualquiera tal que para todo conjunto de Hintikka verifica que si
    \<open>\<not> F\<close> pertenece al conjunto, entonces \<open>F\<close> no pertenece al conjunto.
    Vamos a probar que si \<open>\<not> (\<not> F) \<in> S\<close>, entonces \<open>\<not> F \<notin> S\<close>.
    Supongamos que \<open>\<not> (\<not> F) \<in> S\<close>. Por definición de conjunto de 
    Hintikka, se tiene entonces que \<open>F \<in> S\<close>. Por otra parte, como \<open>S\<close>
    es un conjunto de Hintikka, por hipótesis de inducción se verifica 
    que si \<open>\<not> F \<in> S\<close>, entonces \<open>F \<notin> S\<close>, en contra de lo obtenido 
    anteriormente. Por tanto, por la regla \<open>modus tollens\<close>, \<open>\<not> F \<notin> S\<close>.

    Sea \<open>S\<close> un conjunto de Hintikka. Consideremos la fórmula \<open>G\<close> tal
    que, para cualquier conjunto de Hintikka, si \<open>\<not> G\<close> pertenece al
    conjunto, entonces \<open>G\<close> no pertenece al conjunto. Sea también la
    fórmula \<open>H\<close> que verifica análogamente para cualquier conjunto de 
    Hintikka que, si \<open>\<not> H\<close> pertenece al conjunto, entonces \<open>H\<close> no 
    pertenece al conjunto. Queremos probar que si \<open>\<not> (G \<and> H) \<in> S\<close>,
    entonces \<open>G \<and> H \<notin> S\<close>.\\
    Supongamos que \<open>\<not> (G \<and> H) \<in> S\<close>. Por tanto, por definición de 
    conjunto de Hintikka, \<open>\<not> G \<in> S\<close> o \<open>\<not> H \<in> S\<close>. Veamos que \<open>G \<and> H \<notin> S\<close> 
    por eliminación de la disyunción anterior.\\
    En primer lugar, supongamos que \<open>\<not> G \<in> S\<close>. Entonces,
    como \<open>S\<close> es un conjunto de Hintikka, por hipótesis de inducción 
    tenemos que, \<open>G \<notin> S\<close>. Por propiedades de la conjunción, se observa 
    fácilmente que si \<open>G \<notin> S\<close>, entonces no es cierto que \<open>G \<in> S\<close> y 
    \<open>H \<in> S\<close> simultáneamente.
    Por otro lado, por definición de conjunto de Hintikka, si 
    \<open>G \<and> H \<in> S\<close>, entonces \<open>G \<in> S\<close> y \<open>H \<in> S\<close>, en contra de
    lo obtenido anteriormente. De este modo, por la regla \<open>modus 
    tollens\<close> se obtiene finalmente que \<open>G \<and> H \<notin> S\<close>.\\
    En segundo lugar, supongamos que \<open>\<not> H \<in> S\<close>. Por hipótesis
    de inducción, como \<open>S\<close> es un conjunto de Hintikka, se obtiene que 
    \<open>H \<notin> S\<close>. Razonando igual que en el caso anterior con respecto a la 
    conjunción, como \<open>H \<notin> S\<close>, entonces no es cierto que \<open>G \<in> S\<close> y 
    \<open>H \<in> S\<close> simultáneamente. Por otra parte,  por definición de 
    conjunto de Hintikka, si \<open>G \<and> H \<in> S\<close>, entonces \<open>G \<in> S\<close> y \<open>H \<in> S\<close>,
    en contra de lo obtenido anteriormente. Finalmente, por la regla 
    \<open>modus tollens\<close> se prueba que \<open>G \<and> H \<notin> S\<close>. 

    Sea el conjunto de Hintikka \<open>S\<close>. Consideremos la fórmula \<open>G\<close> tal
    que dado un conjunto de Hintikka cualquiera, si \<open>\<not> G\<close> pertenece a
    dicho conjunto, entonces \<open>G\<close> no pertenece a él. Del mismo modo se
    considera otra fórmula \<open>H\<close> verificando para cualquier conjunto de 
    Hintikka que, si \<open>\<not> H\<close> pertenece al conjunto, entonces \<open>H\<close> no 
    pertence a él. Queremos probar que si \<open>\<not> (G \<or> H) \<in> S\<close>,
    entonces \<open>G \<or> H \<notin> S\<close>.\\
    Supongamos inicialmente que \<open>\<not> (G \<or> H) \<in> S\<close>. Luego, por definición
    de conjunto de Hintikka, se tiene \<open>\<not> G \<in> S\<close> y \<open>\<not> H \<in> S\<close>. En 
    particular, \<open>\<not> G \<in> S\<close>. Como \<open>S\<close> es conjunto de Hintikka, por 
    hipótesis de inducción tenemos entonces que \<open>G \<notin> S\<close>.\\
    Por otra parte, \<open>\<not> H \<in> S\<close> como vimos anteriormente. Luego, al ser 
    \<open>S\<close> un conjunto de Hintikka, aplicando la hipótesis de inducción de 
    manera similar obtenemos que \<open>H \<notin> S\<close>.\\ 
    Resumiendo, hemos probado que \<open>G \<notin> S\<close> y \<open>H \<notin> S\<close>. Es fácil observar 
    que esto implica, en particular, que no es cierto que \<open>G \<in> S\<close> o 
    \<open>H \<in> S\<close>. De nuevo, por definición de conjunto de Hintikka, si 
    \<open>G \<or> H \<in> S\<close>, entonces \<open>G \<in> S\<close> o \<open>H \<in> S\<close>, en contra de lo obtenido
    anteriormente. Por lo tanto, aplicando la regla \<open>modus tollens\<close>, 
    \<open>G \<or> H \<notin> S\<close>.

    Veamos el último caso de la estructura de las fórmulas.
    Consideremos análogamente un conjunto de Hintikka \<open>S\<close>. Sea también
    la fórmula \<open>G\<close> tal que dado cualquier conjunto de Hintikka, si \<open>\<not> G\<close>
    está en el conjunto, entonces \<open>G\<close> no lo está. Del mismo modo se 
    considera la fórmula \<open>H\<close> tal que para un conjunto de Hintikka
    cualquiera verifica que si \<open>\<not> H\<close> pertenece al conjunto, entonces \<open>H\<close> 
    no pertenece al mismo. Vamos a probar que si \<open>\<not> (G \<longrightarrow> H) \<in> S\<close>, 
    entonces \<open>G \<longrightarrow> H \<notin> S\<close>.\\
    Supongamos que \<open>\<not> (G \<longrightarrow> H) \<in> S\<close>. Luego, por definición de conjunto 
    de Hintikka, \<open>G \<in> S\<close> y \<open>\<not> H \<in> S\<close>. En particular, que \<open>G \<in> S\<close>. Como 
    \<open>S\<close> es un conjunto de Hintikka, por hipótesis de inducción se 
    verifica que si \<open>\<not> G \<in> S\<close>, entonces \<open>G \<notin> S\<close>, en contra de lo 
    deducido anteriormente. Por lo tanto, aplicando la regla \<open>modus 
    tollens\<close> obtenemos que \<open>\<not> G \<notin> S\<close>.\\
    Por otro lado, también probamos que \<open>\<not> H \<in> S\<close>. Luego, como 
    \<open>S\<close> es de Hintikka, se obtiene por hipótesis de inducción que 
    \<open>H \<notin> S\<close>.\\ 
    Resumiendo, hemos deducido bajo las condiciones supuestas que 
    \<open>\<not> G \<notin> S\<close> y \<open>H \<notin> S\<close>. Por lo tanto, es fácil observar que no es 
    cierto que \<open>\<not> G \<in> S\<close> o \<open>H \<in> S\<close>. Por definición de conjunto de 
    Hintikka, si \<open>G \<longrightarrow> H \<in> S\<close>, entonces \<open>\<not> G \<in> S\<close> o \<open>H \<in> S\<close>, en contra
    de lo obtenido anteriormente. Por la regla \<open>modus tollens\<close>,
    probamos finalmente que \<open>G \<longrightarrow> H \<notin> S\<close>.
  \end{demostracion}

  Por otra parte, su enunciado se formaliza en Isabelle de la siguiente 
  forma.\<close>

lemma "Hintikka S \<Longrightarrow> (\<^bold>\<not> F \<in> S \<longrightarrow> F \<notin> S)"
  oops

text \<open>Antes de proceder con las distintas pruebas en Isabelle/HOL, 
  vamos a formalizar la regla \<open>modus tollens\<close> usada en las 
  demostraciones. Esta regla no está definida en Isabelle, de modo que 
  se introducirá a continuación como lema auxiliar. Además, mostraremos
  su prueba detallada.\<close>

lemma mt: 
  assumes "F \<longrightarrow> G" 
          "\<not> G"
  shows "\<not> F"
proof -
  have "\<not> G \<longrightarrow> \<not> F"
    using assms(1) by (rule not_mono)
  thus "\<not> F"
    using assms(2) by (rule mp)
qed

text \<open>Procedamos con la demostración del lema en Isabelle/HOL de
  manera detallada. Como es habitual para facilitar dicha prueba, se 
  hará cada caso de la estructura de fórmulas por separado.\<close>

lemma Hintikka_l10_atom: 
  assumes "Hintikka S" 
  shows "\<^bold>\<not> (Atom x) \<in> S \<longrightarrow> Atom x \<notin> S"
proof (rule impI)
  assume "\<^bold>\<not> (Atom x) \<in> S"
  then have "\<not> (\<^bold>\<not> (Atom x) \<notin> S)"
    by (rule contrapos_pn)
  have "Atom x \<in> S \<longrightarrow> \<^bold>\<not> (Atom x) \<notin> S"
    using assms by (rule Hintikka_l2)
  thus "Atom x \<notin> S"
    using \<open>\<not>(\<^bold>\<not> (Atom x) \<notin> S)\<close> by (rule mt)
qed

lemma Hintikka_l10_bot: 
  assumes "Hintikka S" 
  shows "\<^bold>\<not> \<bottom> \<in> S \<longrightarrow> \<bottom> \<notin> S"
proof (rule impI)
  assume "\<^bold>\<not> \<bottom> \<in> S" 
  show "\<bottom> \<notin> S"
    using assms by (rule Hintikka_l1)
qed

lemma Hintikka_l10_not: 
  assumes "Hintikka S \<Longrightarrow> \<^bold>\<not> F \<in> S \<longrightarrow> F \<notin> S"
          "Hintikka S"
        shows "\<^bold>\<not> (\<^bold>\<not> F) \<in> S \<longrightarrow> \<^bold>\<not> F \<notin> S"
proof (rule impI)
  assume "\<^bold>\<not> (\<^bold>\<not> F) \<in> S"
  have "\<^bold>\<not> (\<^bold>\<not> F) \<in> S \<longrightarrow> F \<in> S"
    using assms(2) by (rule Hintikka_l6)
  then have "F \<in> S"
    using \<open>\<^bold>\<not> (\<^bold>\<not> F) \<in> S\<close> by (rule mp)
  then have "\<not> (F \<notin> S)"
    by (rule contrapos_pn)
  have "\<^bold>\<not> F \<in> S \<longrightarrow> F \<notin> S"
    using assms by this
  thus "\<^bold>\<not> F \<notin> S"
    using \<open>\<not> (F \<notin> S)\<close> by (rule mt)
qed

text \<open>Para facilitar las pruebas de los casos correspondientes a las
  conectivas binarias emplearemos los siguientes lemas auxiliares. Estos
  nos permitirán, a partir de la negación de un predicado, introducir 
  la negación de una conjunción o disyunción de dicho predicado con otro
  cualquiera.\<close>

lemma notConj1: 
  assumes "\<not> P"
  shows "\<not> (P \<and> Q)"
proof (rule notI)
  assume "P \<and> Q"
  then have "P"
    by (rule conjunct1)
  show "False"
    using assms \<open>P\<close> by (rule notE)
qed

lemma notConj2: 
  assumes "\<not> Q"
  shows "\<not> (P \<and> Q)"
proof (rule notI)
  assume "P \<and> Q"
  then have "Q"
    by (rule conjunct2)
  show "False"
    using assms \<open>Q\<close> by (rule notE)
qed

lemma notDisj:
  assumes "\<not> P"
          "\<not> Q"
        shows "\<not> (P \<or> Q)"
proof (rule notI)
  assume "P \<or> Q"
  then show "False"
  proof (rule disjE)
    assume "P"
    show "False"
      using assms(1) \<open>P\<close> by (rule notE)
  next
    assume "Q"
    show "False"
      using assms(2) \<open>Q\<close> by (rule notE)
  qed
qed

text \<open>Comencemos las pruebas detalladas de los casos correspondientes a 
  las conectivas binarias. Una vez terminadas, se mostrará la prueba 
  detallada del lema completo.\<close>

lemma Hintikka_l10_and: 
  assumes "Hintikka S \<Longrightarrow> \<^bold>\<not> G \<in> S \<longrightarrow> G \<notin> S"
          "Hintikka S \<Longrightarrow> \<^bold>\<not> H \<in> S \<longrightarrow> H \<notin> S"
          "Hintikka S"
  shows "\<^bold>\<not> (G \<^bold>\<and> H) \<in> S \<longrightarrow> G \<^bold>\<and> H \<notin> S"
proof (rule impI)
  assume "\<^bold>\<not> (G \<^bold>\<and> H) \<in> S"
  have "\<^bold>\<not> (G \<^bold>\<and> H) \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<or> \<^bold>\<not> H \<in> S"
    using assms(3) by (rule Hintikka_l7)
  then have "\<^bold>\<not> G \<in> S \<or> \<^bold>\<not> H \<in> S"
    using \<open>\<^bold>\<not> (G \<^bold>\<and> H) \<in> S\<close> by (rule mp)
  then show "G \<^bold>\<and> H \<notin> S"
  proof (rule disjE)
    assume "\<^bold>\<not> G \<in> S"
    have "\<^bold>\<not> G \<in> S \<longrightarrow> G \<notin> S"
      using assms(1) assms(3) by this
    then have "G \<notin> S"
      using \<open>\<^bold>\<not> G \<in> S\<close> by (rule mp)
    then have "\<not> (G \<in> S \<and> H \<in> S)"
      by (rule notConj1)
    have "G \<^bold>\<and> H \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S"
      using assms(3) by (rule Hintikka_l3)
    thus "G \<^bold>\<and> H \<notin> S"
      using \<open>\<not> (G \<in> S \<and> H \<in> S)\<close>  by (rule mt)
  next
    assume "\<^bold>\<not> H \<in> S"
    have "\<^bold>\<not> H \<in> S \<longrightarrow> H \<notin> S"
      using assms(2) assms(3) by this
    then have "H \<notin> S"
      using \<open>\<^bold>\<not> H \<in> S\<close> by (rule mp)
    then have "\<not> (G \<in> S \<and> H \<in> S)" 
      by (rule notConj2)
    have "G \<^bold>\<and> H \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S"
      using assms(3) by (rule Hintikka_l3)
    thus "G \<^bold>\<and> H \<notin> S"
      using \<open>\<not> (G \<in> S \<and> H \<in> S)\<close> by (rule mt)
  qed
qed

lemma Hintikka_l10_or: 
  assumes "Hintikka S \<Longrightarrow> \<^bold>\<not> G \<in> S \<longrightarrow> G \<notin> S"
          "Hintikka S \<Longrightarrow> \<^bold>\<not> H \<in> S \<longrightarrow> H \<notin> S"
          "Hintikka S"
  shows "\<^bold>\<not> (G \<^bold>\<or> H) \<in> S \<longrightarrow> G \<^bold>\<or> H \<notin> S"
proof (rule impI)
  assume "\<^bold>\<not> (G \<^bold>\<or> H) \<in> S"
  have "\<^bold>\<not> (G \<^bold>\<or> H) \<in> S \<longrightarrow> (\<^bold>\<not> G \<in> S \<and> \<^bold>\<not> H \<in> S)"
    using assms(3) by (rule Hintikka_l8)
  then have C:"\<^bold>\<not> G \<in> S \<and> \<^bold>\<not> H \<in> S"
    using \<open>\<^bold>\<not> (G \<^bold>\<or> H) \<in> S\<close> by (rule mp)
  then have "\<^bold>\<not> G \<in> S"
    by (rule conjunct1)
  have "\<^bold>\<not> G \<in> S \<longrightarrow> G \<notin> S"
    using assms(1) assms(3) by this
  then have "G \<notin> S" 
    using \<open>\<^bold>\<not> G \<in> S\<close> by (rule mp) 
  have "\<^bold>\<not> H \<in> S"
    using C by (rule conjunct2)
  have "\<^bold>\<not> H \<in> S \<longrightarrow> H \<notin> S"
    using assms(2) assms(3) by this
  then have "H \<notin> S" 
    using \<open>\<^bold>\<not> H \<in> S\<close> by (rule mp)
  have "\<not> (G \<in> S \<or> H \<in> S)"
    using \<open>G \<notin> S\<close> \<open>H \<notin> S\<close> by (rule notDisj)
  have "(G \<^bold>\<or> H \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S)"
    using assms(3) by (rule Hintikka_l4)
  thus "G \<^bold>\<or> H \<notin> S"
    using \<open>\<not> (G \<in> S \<or> H \<in> S)\<close> by (rule mt)
qed

lemma Hintikka_l10_imp: 
  assumes "Hintikka S \<Longrightarrow> \<^bold>\<not> G \<in> S \<longrightarrow> G \<notin> S"
          "Hintikka S \<Longrightarrow> \<^bold>\<not> H \<in> S \<longrightarrow> H \<notin> S"
          "Hintikka S"
  shows "\<^bold>\<not> (G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> G \<^bold>\<rightarrow> H \<notin> S"
proof (rule impI)
  assume "\<^bold>\<not> (G \<^bold>\<rightarrow> H) \<in> S"
  have "\<^bold>\<not> (G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> (G \<in> S \<and> \<^bold>\<not> H \<in> S)"
    using assms(3) by (rule Hintikka_l9)
  then have C:"G \<in> S \<and> \<^bold>\<not> H \<in> S"
    using \<open>\<^bold>\<not> (G \<^bold>\<rightarrow> H) \<in> S\<close> by (rule mp)
  then have "G \<in> S"
    by (rule conjunct1)
  then have "\<not> (G \<notin> S)"
    by (rule contrapos_pn)
  have "\<^bold>\<not> G \<in> S \<longrightarrow> G \<notin> S"
    using assms(1) assms(3) by this
  then have "\<^bold>\<not> G \<notin> S"
    using \<open>\<not> (G \<notin> S)\<close> by (rule mt)
  have "\<^bold>\<not> H \<in> S"
    using C by (rule conjunct2)
  have "\<^bold>\<not> H \<in> S \<longrightarrow> H \<notin> S"
    using assms(2) assms(3) by this
  then have "H \<notin> S"
    using \<open>\<^bold>\<not> H \<in> S\<close> by (rule mp)
  have "\<not> (\<^bold>\<not> G \<in> S \<or> H \<in> S)"
    using \<open>\<^bold>\<not> G \<notin> S\<close> \<open>H \<notin> S\<close> by (rule notDisj)
  have "G \<^bold>\<rightarrow> H \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<or> H \<in> S"
    using assms(3) by (rule Hintikka_l5)
  thus "G \<^bold>\<rightarrow> H \<notin> S"
    using \<open>\<not> (\<^bold>\<not> G \<in> S \<or> H \<in> S)\<close> by (rule mt)
qed

lemma "Hintikka S \<Longrightarrow> \<^bold>\<not> F \<in> S \<longrightarrow> F \<notin> S"
proof (induct F)
case (Atom x)
  then show ?case by (rule Hintikka_l10_atom)
next
  case Bot
  then show ?case by (rule Hintikka_l10_bot)
next
  case (Not F)
  then show ?case by (rule Hintikka_l10_not)
next
  case (And F1 F2)
  then show ?case by (rule Hintikka_l10_and)
next
  case (Or F1 F2)
  then show ?case by (rule Hintikka_l10_or)
next
  case (Imp F1 F2)
  then show ?case by (rule Hintikka_l10_imp)
qed

text \<open>Por último, su demostración automática es la que sigue.\<close>

lemma Hintikka_l10: 
 "Hintikka S \<Longrightarrow> \<^bold>\<not> F \<in> S \<longrightarrow> F \<notin> S"
  apply (induct F)
  apply (meson Hintikka_l2)
  apply (simp add: Hintikka_l1)
  using Hintikka_l6 apply blast
  using Hintikka_l3 Hintikka_l7 apply blast
  apply (smt Hintikka_def)
  using Hintikka_l5 Hintikka_l9 by blast

section \<open>Lema de Hintikka\<close>

text \<open>Una vez definida la noción de conjunto de Hintikka y conocidas las
  propiedades que se deducen de ella, nuestro objetivo será demostrar
  que todo conjunto de Hintikka es satisfacible.

  Por definición, para probar que un conjunto es satisfacible basta
  hallar una interpretación que sea modelo suyo. De este modo, definimos 
  el siguiente tipo de interpretaciones.

  \begin{definicion}
    Sea un conjunto de fórmulas cualquiera. Se define la \<open>interpretación 
    asociada al conjunto\<close> como aquella que devuelve \<open>Verdadero\<close> sobre 
    las variables proposicionales cuya correspondiente fórmula 
    atómica pertence al conjunto, y \<open>Falso\<close> en caso contrario.
  \end{definicion}

  En Isabelle se formalizará mediante el tipo \<open>definition\<close> como se
  expone a continuación.\<close>

definition setValuation :: 
   "('a formula) set \<Rightarrow> 'a valuation" where
    "setValuation S  \<equiv> \<lambda>k. Atom k \<in> S"

text \<open>Presentemos ahora ejemplos del valor de ciertas fórmulas 
  en la interpretación asociada a los conjuntos siguientes.\<close>

notepad
begin

  have "(setValuation {Atom 0 \<^bold>\<and> ((\<^bold>\<not> (Atom 1)) \<^bold>\<rightarrow> Atom 2), 
            ((\<^bold>\<not> (Atom 1)) \<^bold>\<rightarrow> Atom 2), Atom 0,
            \<^bold>\<not>(\<^bold>\<not> (Atom 1)), Atom 1}) \<Turnstile> Atom 1 \<^bold>\<rightarrow> Atom 0 = True"
    unfolding setValuation_def by simp

  have "(setValuation {Atom 3 \<^bold>\<or> (\<^bold>\<not> (Atom 1)), 
            \<^bold>\<not> (\<^bold>\<not> (Atom 6))}) \<Turnstile> Atom 2 \<^bold>\<or> Atom 6 = False"
    unfolding setValuation_def by simp

end

text \<open>Previamente a probar que los conjuntos de Hintikka son 
  satisfacibles y con el fin de facilitar dicha demostración, 
  introducimos el siguiente resultado.

  \begin{lema}
    La interpretación asociada a un conjunto de Hintikka es modelo de
    una fórmula si esta pertenece al conjunto. Además, dicha 
    interpretación no es modelo de una fórmula si su negación 
    pertenece al conjunto.
  \end{lema}

  Su formalización en Isabelle es la siguiente.\<close>

lemma "Hintikka S \<Longrightarrow> (F \<in> S \<longrightarrow> isModel (setValuation S) F)
           \<and> (\<^bold>\<not> F \<in> S \<longrightarrow> (\<not> (isModel (setValuation S) F)))"
  oops

text \<open>Procedamos a la demostración del resultado.

  \begin{demostracion}
    El lema se prueba mediante inducción en la estructura de las
    fórmulas. Como es habitual, se distinguen los siguientes casos.

    En primer lugar, consideremos el conjunto de Hintikka \<open>S\<close>. Queremos
    probar que, dada una variable proposicional \<open>p\<close> cualquiera, se
    verifica:
    \begin{enumerate} 
      \item La interpretación asociada a \<open>S\<close> es modelo de \<open>p\<close> si
        \<open>p \<in> S\<close>.
      \item La interpretación asociada a \<open>S\<close> no es modelo de \<open>p\<close> si 
        \<open>\<not> p \<in> S\<close>.
    \end{enumerate}
    Veamos la primera afirmación. Para ello, supongamos que \<open>p \<in> S\<close>. En 
    este caso, por definición de la interpretación asociada al conjunto
    \<open>S\<close>, la imagen de la variable \<open>p\<close> por dicha interpretación es 
    \<open>Verdadero\<close>. Luego, por definición del valor de una fórmula atómica 
    en una interpretación, el valor de \<open>p\<close> en la interpretación 
    asociada a \<open>S\<close> es \<open>Verdadero\<close>. Por tanto, la
    interpretación asociada a \<open>S\<close> es modelo de \<open>p\<close>.\\
    Por otra parte, demostremos la segunda afirmación. Supongamos
    que \<open>\<not> p \<in> S\<close>. Por un lema anterior, como \<open>S\<close> es de Hintikka, 
    entonces \<open>p \<notin> S\<close>. De este modo, la imagen de la variable \<open>p\<close> por la 
    interpretación asociada a \<open>S\<close> es \<open>Falso\<close>. Análogamente, por 
    definición del valor de una fórmula atómica en una interpretación,
    obtenemos que el valor de la fórmula \<open>p\<close> en dicha interpretación
    es \<open>Falso\<close>. Finalmente, por definición de modelo, la interpretación 
    asociada al conjunto \<open>S\<close> no es modelo de \<open>p\<close>, como queríamos probar.
 
    Probemos ahora el resultado para la fórmula \<open>\<bottom>\<close> dado un conjunto de
    Hintikka cualquiera \<open>S\<close>. Análogamente, vamos a demostrar dos
    afirmaciones:
    \begin{enumerate}
      \item La interpretación asociada a \<open>S\<close> es modelo de \<open>\<bottom>\<close> si 
        \<open>\<bottom> \<in> S\<close>.
      \item La interpretación asociada a \<open>S\<close> no es modelo de \<open>\<bottom>\<close> si 
        \<open>\<not> \<bottom> \<in> S\<close>.
    \end{enumerate}
    Probemos la primera afirmación. Supongamos que \<open>\<bottom> \<in> S\<close>. Por 
    definición de conjunto de Hintikka, sabemos que \<open>\<bottom> \<notin> S\<close>, de modo 
    que hemos llegado a una contradicción. Luego, en particular, 
    tenemos el resultado.\\
    Demostremos a continuación la segunda afirmación. Supongamos que 
    \<open>\<not> \<bottom> \<in> S\<close>. Como el valor de \<open>\<bottom>\<close> es \<open>Falso\<close> en toda interpretación, 
    en particular lo es en la interpretación asociada al conjunto \<open>S\<close>. 
    De este modo, dicha interpretación no es modelo de \<open>\<bottom>\<close>, como 
    queríamos demostrar.

    Consideremos ahora el conjunto de Hintikka \<open>S\<close> cualquiera. Suponemos
    que, para toda fórmula \<open>F\<close>, la interpretación asociada a \<open>S\<close> es 
    modelo de \<open>F\<close> si \<open>F \<in> S\<close>, y no es modelo de \<open>F\<close> si \<open>\<not> F \<in> S\<close>. Vamos 
    a probar las siguientes afirmaciones:
    \begin{enumerate}
      \item La interpretación asociada a \<open>S\<close> es modelo de \<open>\<not> F\<close> si 
        \<open>\<not> F \<in> S\<close>.
      \item La interpretación asociada a \<open>S\<close> no es modelo de \<open>\<not> F\<close> si 
        \<open>\<not> (\<not> F) \<in> S\<close>.
    \end{enumerate}
    Probemos la primera afirmación. Supongamos que, fijada una fórmula
    cualquiera \<open>F\<close>, se tiene que \<open>\<not> F \<in> S\<close>. Por hipótesis de inducción, 
    tenemos pues que la interpretación asociada a \<open>S\<close> no es modelo de 
    \<open>F\<close>. En otras palabras, no es cierto que el valor de \<open>F\<close> en esta 
    interpretación sea \<open>Verdadero\<close>. Por definición del valor de la 
    negación de una fórmula en una interpretación, esto es equivalente a 
    que el valor de la fórmula \<open>\<not> F\<close> en la interpretación asociada a \<open>S\<close> 
    sea \<open>Verdadero\<close>. Por lo tanto, dicha interpretación es modelo de 
    \<open>\<not> F\<close>.\\
    Por otra parte, probemos la segunda afirmación fijada una fórmula
    \<open>F\<close> cualquiera. Supongamos que \<open>\<not> (\<not> F) \<in> S\<close>. Luego, por definición 
    de conjunto de Hintikka, \<open>F \<in> S\<close>. Además, por hipótesis de 
    inducción, se tiene entonces que la interpretación asociada a \<open>S\<close> es 
    modelo de \<open>F\<close>. En otras palabras, no es cierto que dicha 
    interpretación no sea modelo de \<open>F\<close>. Por definición de ser modelo de 
    una fórmula, no es cierto que el valor de \<open>F\<close> en dicha 
    interpretación no sea \<open>Verdadero\<close>. Análogamente, por definición del 
    valor de la negación de una fórmula en una interpretación, tenemos 
    que esto es equivalente a asumir que no es cierto que el valor de 
    \<open>\<not> F\<close> en la interpretación asociada a \<open>S\<close> sea \<open>Verdadero\<close>. Por lo 
    tanto, esta interpretación no es modelo de \<open>\<not> F\<close>, como queríamos 
    demostrar. 

    Veamos el siguiente caso de la estructura de las fórmulas. Sea \<open>S\<close>
    un conjunto de Hintikka. Se considera que, para toda fórmula \<open>F\<^sub>1\<close> y 
    \<open>F\<^sub>2\<close>, la interpretación asociada a \<open>S\<close> es modelo de \<open>F\<^sub>i\<close> si
    \<open>F\<^sub>i \<in> S\<close> para \<open>i = 1,2\<close>. Además, se verifica que
    dicha interpretación no es modelo de \<open>F\<^sub>i\<close> si \<open>\<not> F\<^sub>i \<in> S\<close> para 
    \<open>i=1,2\<close>. Hay que probar que se tienen las siguientes afirmaciones:
    \begin{enumerate}
      \item La interpretación asociada a \<open>S\<close> es modelo de \<open>F\<^sub>1 \<and> F\<^sub>2\<close> si 
        \<open>F\<^sub>1 \<and> F\<^sub>2 \<in> S\<close>.
      \item La interpretación asociada a \<open>S\<close> no es modelo de \<open>F\<^sub>1 \<and> F\<^sub>2\<close> 
        si \<open>\<not>(F\<^sub>1 \<and> F\<^sub>2) \<in> S\<close>.
    \end{enumerate}
    Probemos la primera afirmación. Supongamos, pues, fijadas las
    fórmulas \<open>F\<^sub>1\<close> y \<open>F\<^sub>2\<close> cualesquiera, se tiene que \<open>F\<^sub>1 \<and> F\<^sub>2 \<in> S\<close>.
    Luego, por definición de conjunto de Hintikka, se tiene que \<open>F\<^sub>1 \<in> S\<close> 
    y \<open>F\<^sub>2 \<in> S\<close>. En particular, \<open>F\<^sub>1 \<in> S\<close> y, por hipótesis de
    inducción, la interpretación asociada a \<open>S\<close> es modelo de \<open>F\<^sub>1\<close>. En
    otras palabras, el valor de \<open>F\<^sub>1\<close> en la interpretación asociada a
    \<open>S\<close> es \<open>Verdadero\<close>. Por otra parte, también obtuvimos que \<open>F\<^sub>2 \<in> S\<close>. 
    Razonando de manera análoga, por hipótesis de inducción se verifica 
    entonces que la interpretación asociada a \<open>S\<close> es modelo de \<open>F\<^sub>2\<close>. Es 
    decir, el valor de \<open>F\<^sub>2\<close> en dicha interpretación es \<open>Verdadero\<close>. 
    Resumiendo, hemos obtenido que el valor de \<open>F\<^sub>1\<close> en la interpretación 
    asociada a \<open>S\<close> es \<open>Verdadero\<close> y el valor de \<open>F\<^sub>2\<close> en dicha 
    interpretación también es \<open>Verdadero\<close>. Por definición del valor de 
    la conjunción de dos fórmulas en una interpretación, tenemos 
    equivalentemente que el valor de \<open>F\<^sub>1 \<and> F\<^sub>2\<close> en la interpretación 
    asociada a \<open>S\<close> es \<open>Verdadero\<close>. Por tanto, la interpretación asociada 
    a \<open>S\<close> es modelo de \<open>F\<^sub>1 \<and> F\<^sub>2\<close>.\\
    Probemos ahora la segunda afirmación fijadas las fórmulas
    \<open>F\<^sub>1\<close> y \<open>F\<^sub>2\<close>. Supongamos que \<open>\<not>(F\<^sub>1 \<and> F\<^sub>2) \<in> S\<close>. Entonces, por
    definición de conjunto de Hintikka, \<open>\<not> F\<^sub>1 \<in> S\<close> o \<open>\<not> F\<^sub>2 \<in> S\<close>. Veamos 
    que la interpretación asociada a \<open>S\<close> no es modelo de 
    \<open>F\<^sub>1 \<and> F\<^sub>2\<close> mediante la eliminación de la disyunción anterior.\\
    En primer lugar supongamos que \<open>\<not> F\<^sub>1 \<in> S\<close>. Como \<open>S\<close> es un conjunto
    de Hintikka, por hipótesis de inducción obtenemos que la 
    interpretación asociada a \<open>S\<close> no es modelo de \<open>F\<^sub>1\<close>. Esto significa 
    que el valor de \<open>F\<^sub>1\<close> en la interpretación asociada a \<open>S\<close>
    no es \<open>Verdadero\<close>. Por tanto, no es cierto afirmar que el valor de 
    \<open>F\<^sub>1\<close> y \<open>F\<^sub>2\<close> en dicha interpretación es \<open>Verdadero\<close>. Por definición 
    del valor de la conjunción de dos fórmulas en una interpretación, 
    tenemos equivalentemenete que no es cierto que el valor de \<open>F\<^sub>1 \<and> F\<^sub>2\<close> 
    en la interpretación asociada a \<open>S\<close> sea \<open>Verdadero\<close>, luego dicha 
    interpretación no es modelo de esta fórmula.\\
    Por otro lado, supongamos ahora que \<open>\<not> F\<^sub>2 \<in> S\<close>. Razonando de la 
    misma manera, al ser \<open>S\<close> de Hintikka se obtiene, por hipótesis de 
    inducción, que la interpretación asociada a \<open>S\<close> no es modelo de 
    \<open>F\<^sub>2\<close>. Es decir, el valor de \<open>F\<^sub>2\<close> en dicha interpretación no es 
    \<open>Verdadero\<close>. Por lo tanto, se puede afirmar que no es cierto que 
    tanto el valor de \<open>F\<^sub>1\<close> como el de \<open>F\<^sub>2\<close> en la interpretación asociada 
    a \<open>S\<close> sean \<open>Verdadero\<close>. Por la definición del valor de la conjunción 
    de dos fórmulas en una interpretación, equivalentemente no es cierto 
    que el valor de \<open>F\<^sub>1 \<and> F\<^sub>2\<close> en la interpretación asociada a \<open>S\<close> es 
    \<open>Verdadero\<close>. Por tanto, dicha interpretación no es modelo de 
    \<open>F\<^sub>1 \<and> F\<^sub>2\<close>, como se quería probar.

    Consideremos de nuevo \<open>S\<close> un conjunto de Hintikka cualquiera.\\ 
    Suponemos análogamente que para toda fórmula \<open>F\<^sub>1\<close> y \<open>F\<^sub>2\<close>, la 
    interpretación asociada a \<open>S\<close> es modelo de \<open>F\<^sub>i\<close> si \<open>F\<^sub>i \<in> S\<close> para 
    \<open>i = 1,2\<close>. Además, se verifica que dicha interpretación no 
    es modelo de \<open>F\<^sub>i\<close> si \<open>\<not> F\<^sub>i \<in> S\<close> para \<open>i=1,2\<close>. Vamos a probar que 
    se verifican las siguientes afirmaciones:
    \begin{enumerate}
      \item La interpretación asociada a \<open>S\<close> es modelo de \<open>F\<^sub>1 \<or> F\<^sub>2\<close> si 
        \<open>F\<^sub>1 \<or> F\<^sub>2 \<in> S\<close>.
      \item La interpretación asociada a \<open>S\<close> no es modelo de \<open>F\<^sub>1 \<or> F\<^sub>2\<close> 
        si \<open>\<not>(F\<^sub>1 \<or> F\<^sub>2) \<in> S\<close>.
    \end{enumerate}
    Demostremos la primera afirmación. Supongamos que, fijadas las 
    fórmulas \<open>F\<^sub>1\<close> y \<open>F\<^sub>2\<close>, tenemos que \<open>F\<^sub>1 \<or> F\<^sub>2 \<in> S\<close>. Por definición
    de conjunto de Hintikka, se obtiene entonces que \<open>F\<^sub>1 \<in> S\<close> o 
    \<open>F\<^sub>2 \<in> S\<close>. Vamos a probar que la interpretación asociada a \<open>S\<close> es 
    modelo de \<open>F\<^sub>1 \<or> F\<^sub>2\<close> mediante la eliminación de la disyunción 
    anterior.\\
    Supongamos que \<open>F\<^sub>1 \<in> S\<close>. Por hipótesis de inducción, como \<open>S\<close> es de
    Hintikka, obtenemos entonces que la interpretación asociada a \<open>S\<close> 
    es modelo de \<open>F\<^sub>1\<close>. Es decir, el valor de \<open>F\<^sub>1\<close> en dicha 
    interpretación es \<open>Verdadero\<close>. Por lo tanto, se puede afirmar que, 
    o bien el valor de \<open>F\<^sub>1\<close> en la interpretación asociada a \<open>S\<close> es 
    \<open>Verdadero\<close>, o bien lo es el valor de \<open>F\<^sub>2\<close> en la misma 
    interpretación. Por la definición del valor de la disyunción de dos 
    fórmulas en una interpretación, esto equivale a afirmar que el valor 
    de \<open>F\<^sub>1 \<or> F\<^sub>2\<close> en la interpretación asociada a \<open>S\<close> es \<open>Verdadero\<close>. 
    Luego, dicha interpretación es modelo de \<open>F\<^sub>1 \<or> F\<^sub>2\<close>.\\
    Por otro lado, supongamos que \<open>F\<^sub>2 \<in> S\<close>. Análogamente, como \<open>S\<close> es
    de Hintikka, por hipótesis de inducción se deduce que la 
    interpretación asociada a \<open>S\<close> es modelo de \<open>F\<^sub>2\<close>. En otras palabras, 
    el valor de \<open>F\<^sub>2\<close> en la interpretación asociada a \<open>S\<close> es \<open>Verdadero\<close>. 
    De este modo se puede afirmar que, o bien el valor de \<open>F\<^sub>1\<close> en esta
    interpretación es \<open>Verdadero\<close>, o bien lo es el de \<open>F\<^sub>2\<close> en la misma
    interpretación. Por definición del valor de la disyunción de dos
    fórmulas en una interpretación, esto es equivalente a afirmar que
    el valor de \<open>F\<^sub>1 \<or> F\<^sub>2\<close> es \<open>Verdadero\<close> para la interpretación
    asociada a \<open>S\<close>, luego dicha interpretación es modelo de la
    fórmula.\\
    Veamos, ahora, la segunda afirmación. Fijadas las fórmulas \<open>F\<^sub>1\<close> y 
    \<open>F\<^sub>2\<close>,\\ suponemos inicialmente que \<open>\<not>(F\<^sub>1 \<or> F\<^sub>2) \<in> S\<close>. Por
    definición de conjunto de Hintikka, tenemos entonces que
    \<open>\<not> F\<^sub>1 \<in> S\<close> y \<open>\<not> F\<^sub>2 \<in> S\<close>. En particular, \<open>\<not> F\<^sub>1 \<in> S\<close> luego 
    como \<open>S\<close> es de Hintikka, se tiene por hipótesis de inducción que la 
    interpretación asociada a \<open>S\<close> no es modelo de \<open>F\<^sub>1\<close>. Es decir, el 
    valor de \<open>F\<^sub>1\<close> en la interpretación asociada a \<open>S\<close> no es \<open>Verdadero\<close>. 
    Por otra parte, deducimos también que \<open>\<not> F\<^sub>2 \<in> S\<close>. Análogamente, por 
    hipótesis de inducción tenemos entonces que la interpretación 
    asociada a \<open>S\<close> no es modelo de \<open>F\<^sub>2\<close>. Luego el valor de \<open>F\<^sub>2\<close> en dicha 
    interpretación no es \<open>Verdadero\<close>.\\
    Resumiendo, hemos obtenido que ni el valor de \<open>F\<^sub>1\<close> en la
    interpretación asociada a \<open>S\<close> es \<open>Verdadero\<close>, ni el valor de \<open>F\<^sub>2\<close>
    en la misma interpretación es \<open>Verdadero\<close>. Luego, se puede afirmar
    que no es cierto que el valor de \<open>F\<^sub>1\<close> o el valor de \<open>F\<^sub>2\<close> en la 
    interpretación asociada a \<open>S\<close> sea \<open>Verdadero\<close>. Otra vez más, por
    la definición del valor de la disyunción de dos fórmulas en una
    interpretación, lo anterior es equivalente a afirmar que el valor
    de \<open>F\<^sub>1 \<or> F\<^sub>2\<close> en la interpretación asociada a \<open>S\<close> no es \<open>Verdadero\<close>. 
    Por lo tanto, esta interpretación no es modelo de \<open>F\<^sub>1 \<or> F\<^sub>2\<close>, como
    se quería probar.

    Concluyamos con la prueba del caso de la última conectiva binaria.
    Sea \<open>S\<close> un conjunto de Hintikka cualquiera. Consideramos 
    análogamente que, para toda fórmula \<open>F\<^sub>1\<close> y \<open>F\<^sub>2\<close>, la interpretación 
    asociada a \<open>S\<close> es modelo de \<open>F\<^sub>i\<close> si \<open>F\<^sub>i \<in> S\<close> para \<open>i = 1,2\<close>. Además, 
    se verifica que dicha interpretación no es modelo de \<open>F\<^sub>i\<close> si 
    \<open>\<not> F\<^sub>i \<in> S\<close> para \<open>i=1,2\<close>. Se quieren probar las siguientes 
    afirmaciones:
    \begin{enumerate}
      \item La interpretación asociada a \<open>S\<close> es modelo de \<open>F\<^sub>1 \<rightarrow> F\<^sub>2\<close> si 
        \<open>F\<^sub>1 \<rightarrow> F\<^sub>2 \<in> S\<close>. 
      \item La interpretación asociada a \<open>S\<close> no es modelo de \<open>F\<^sub>1 \<rightarrow> F\<^sub>2\<close> 
        si\\ \<open>\<not>(F\<^sub>1 \<rightarrow> F\<^sub>2) \<in> S\<close>.
    \end{enumerate}
    Probemos la primera. Para ello, fijadas las fórmulas \<open>F\<^sub>1\<close> y \<open>F\<^sub>2\<close>, 
    supongamos que \<open>F\<^sub>1 \<rightarrow> F\<^sub>2 \<in> S\<close>. Entonces, por definición de conjunto 
    de Hintikka, tenemos que \<open>\<not> F\<^sub>1 \<in> S\<close> o \<open>F\<^sub>2 \<in> S\<close>. Vamos a probar que 
    la interpretación asociada a \<open>S\<close> es modelo de \<open>F\<^sub>1 \<rightarrow> F\<^sub>2\<close> mediante la
    eliminación de la disyunción anterior.\\
    Consideremos el caso en que \<open>\<not> F\<^sub>1 \<in> S\<close>. Por tanto, al ser \<open>S\<close> de
    Hintikka, se obtiene por hipótesis de inducción que la 
    interpretación asociada a \<open>S\<close> no es modelo de \<open>F\<^sub>1\<close>, es decir, el 
    valor de \<open>F\<^sub>1\<close> en esta interpretación no es \<open>Verdadero\<close>. Veamos ahora 
    que si el valor de \<open>F\<^sub>1\<close> en la interpretación asociada a \<open>S\<close> es 
    \<open>Verdadero\<close>, entonces el valor de \<open>F\<^sub>2\<close> en esta interpretación es 
    también \<open>Verdadero\<close>.\\
    Supongamos, pues, que el valor de \<open>F\<^sub>1\<close> en la interpretación
    asociada a \<open>S\<close> fuese \<open>Verdadero\<close>. Como anteriormente deducimos
    que no lo era, hemos llegado a una contradicción. Luego,
    en particular, se prueba que el valor de \<open>F\<^sub>2\<close> en esta interpretación 
    es \<open>Verdadero\<close>.\\
    Por tanto, hemos probado que si el valor de \<open>F\<^sub>1\<close> es \<open>Verdadero\<close> en
    la interpretación asociada a \<open>S\<close>, también lo es el valor de \<open>F\<^sub>2\<close>
    en dicha interpretación. Por definición del valor de la implicación
    de dos fórmulas en una interpretación, esto es equivalente a que
    el valor de \<open>F\<^sub>1 \<rightarrow> F\<^sub>2\<close> sea \<open>Verdadero\<close> en la interpretación
    asociada a \<open>S\<close>, como queríamos probar.\\
    Supongamos ahora el caso en que \<open>F\<^sub>2\<close> pertenezca a \<open>S\<close>. Por tanto,
    como \<open>S\<close> es de Hintikka, se obtiene por hipótesis de inducción que 
    la interpretación asociada a \<open>S\<close> es modelo de \<open>F\<^sub>2\<close>. En otras 
    palabras, el valor de \<open>F\<^sub>2\<close> dada dicha interpretación es \<open>Verdadero\<close>. 
    Vamos a probar que, si el valor de \<open>F\<^sub>1\<close> en la interpretación 
    asociada a \<open>S\<close> es \<open>Verdadero\<close>, entonces el valor de \<open>F\<^sub>2\<close> también lo 
    es en esta interpretación.\\
    Supongamos que el valor de \<open>F\<^sub>1\<close> es \<open>Verdadero\<close> en la interpretación
    asociada a \<open>S\<close>. Entonces, como se dedujo anteriormente el valor de 
    \<open>F\<^sub>2\<close> es también \<open>Verdadero\<close> en dicha interpretación.\\
    Probado esto, por definición del valor de la implicación de dos 
    fórmulas en una interpretación, se obtiene equivalentemente que
    el valor de \<open>F\<^sub>1 \<rightarrow> F\<^sub>2\<close> es \<open>Verdadero\<close> en la interpretación asociada 
    a \<open>S\<close>, como queríamos demostrar.\\
    Probemos, finalmente, la segunda afirmación. Supongamos pues, 
    fijadas las fórmulas \<open>F\<^sub>1\<close> y \<open>F\<^sub>2\<close>, que \<open>\<not>(F\<^sub>1 \<rightarrow> F\<^sub>2) \<in> S\<close>. Luego,
    por definición de conjunto de Hintikka, \<open>F\<^sub>1 \<in> S\<close> y \<open>\<not> F\<^sub>2 \<in> S\<close>.
    En particular, \<open>F\<^sub>1 \<in> S\<close> luego, al ser \<open>S\<close> de Hintikka, tenemos por 
    hipótesis de inducción que la interpretación asociada a \<open>S\<close> 
    es modelo de \<open>F\<^sub>1\<close>. Es decir, el valor de esta fórmula es \<open>Verdadero\<close> 
    en dicha interpretación. Análogamente, como hemos visto que\\ 
    \<open>\<not> F\<^sub>2 \<in> S\<close>, aplicando hipótesis de inducción se obtiene que la 
    interpretación asociada a \<open>S\<close> no es modelo de \<open>F\<^sub>2\<close>. Luego, el valor 
    de \<open>F\<^sub>2\<close> no es \<open>Verdadero\<close> en esta interpretación. Veamos que no es 
    cierto que si el valor de \<open>F\<^sub>1\<close> en la interpretación asociada a \<open>S\<close> 
    es \<open>Verdadero\<close>, entonces el valor de \<open>F\<^sub>2\<close> en dicha interpretación 
    también lo es.\\
    Para ello, supongamos lo contrario: si el valor de \<open>F\<^sub>1\<close> en la 
    interpretación asociada a \<open>S\<close> es \<open>Verdadero\<close>, entonces el valor de 
    \<open>F\<^sub>2\<close> en dicha interpretación también lo es. Como anteriormente vimos 
    que el valor de \<open>F\<^sub>1\<close> en la interpretación asociada a \<open>S\<close> es 
    \<open>Verdadero\<close>, tendríamos entonces que el valor de \<open>F\<^sub>2\<close> también lo es 
    en esta interpretación. De este modo, hemos llegado a una 
    contradicción, pues anteriormente demostramos que el valor de \<open>F\<^sub>2\<close> 
    no era \<open>Verdadero\<close> en esta interpretación.\\
    En conclusión, hemos demostrado que no es cierto que si el valor de 
    \<open>F\<^sub>1\<close> en la interpretación asociada a \<open>S\<close> es \<open>Verdadero\<close>, entonces 
    el valor de \<open>F\<^sub>2\<close> en dicha interpretación también lo es. Por
    definición del valor de la implicación de dos fórmulas en una
    interpretación, esto es equivalente a afirmar que no es cierto que
    el valor de \<open>F\<^sub>1 \<rightarrow> F\<^sub>2\<close> en la interpretación asociada a \<open>S\<close> sea
    \<open>Verdadero\<close>. Por tanto, dicha interpretación no es modelo de la
    fórmula, probando así el resultado.
  \end{demostracion}

  Una vez terminada la prueba anterior, procedemos a las distintas
  demostraciones del lema mediante Isabelle/HOL. En primer lugar
  aparecerán las demostraciones detalladas de cada caso de la estructura
  de las fórmulas por separado. Posteriormente se mostrará la prueba
  detallada del lema completo.\<close>

lemma
  assumes  "Hintikka S"
  shows "\<And>x. (Atom x \<in> S \<longrightarrow> isModel (setValuation S) (Atom x)) \<and>
         (\<^bold>\<not> (Atom x) \<in> S \<longrightarrow> \<not> isModel (setValuation S) (Atom x))"
proof (rule conjI)
  show "\<And>x. Atom x \<in> S \<longrightarrow> isModel (setValuation S) (Atom x)" 
  proof
    fix x
    assume "Atom x \<in> S"
    hence "(setValuation S) x"
      by (simp only: setValuation_def)
    hence "setValuation S \<Turnstile> Atom x"
      by (simp only: formula_semantics.simps(1))
    thus "isModel (setValuation S) (Atom x)"
      by (simp only: isModel_def)
  qed
next 
  show 
  "\<And>x. \<^bold>\<not> (Atom x) \<in> S \<longrightarrow> \<not> isModel (setValuation S) (Atom x)" 
  proof
    fix x
    assume "\<^bold>\<not> (Atom x) \<in> S" 
    have "\<^bold>\<not> (Atom x) \<in> S \<longrightarrow> Atom x \<notin> S"
      using assms by (rule Hintikka_l10)
    then have "Atom x \<notin> S"
      using \<open>\<^bold>\<not> (Atom x) \<in> S\<close> by (rule mp)
    also have "(\<not> (Atom x \<in> S)) = (\<not> (setValuation S) x)"
      by (simp only: setValuation_def)
    also have "\<dots> = (\<not> ((setValuation S) \<Turnstile> (Atom x)))"
      by (simp only: formula_semantics.simps(1))
    also have "\<dots> = (\<not> isModel (setValuation S) (Atom x))" 
      by (simp only: isModel_def)
    finally show "\<not> isModel (setValuation S) (Atom x)"
      by this
  qed
qed

lemma Hl2_1:
  assumes  "Hintikka S"
  shows "\<And>x. (Atom x \<in> S \<longrightarrow> isModel (setValuation S) (Atom x)) \<and>
         (\<^bold>\<not> (Atom x) \<in> S \<longrightarrow> \<not> isModel (setValuation S) (Atom x))"
  by (simp add: Hintikka_l10 assms isModel_def setValuation_def)

lemma 
  assumes "Hintikka S"
  shows "(\<bottom> \<in> S \<longrightarrow> isModel (setValuation S) \<bottom>)
           \<and> (\<^bold>\<not> \<bottom> \<in> S \<longrightarrow> (\<not>(isModel (setValuation S) \<bottom>)))"
proof (rule conjI)
  show "\<bottom> \<in> S \<longrightarrow> isModel (setValuation S) \<bottom>"
  proof (rule impI)
    assume "\<bottom> \<in> S"
    have "\<bottom> \<notin> S" 
      using assms by (rule Hintikka_l1)
    thus "isModel (setValuation S) \<bottom>"
      using \<open>\<bottom> \<in> S\<close> by (rule notE)
  qed
next
  show "\<^bold>\<not> \<bottom> \<in> S \<longrightarrow> \<not> isModel (setValuation S) \<bottom>"
  proof (rule impI)
    assume "\<^bold>\<not> \<bottom> \<in> S"
    have "\<not> (setValuation S) \<Turnstile> \<bottom>"
    proof (rule notI)
     assume "setValuation S \<Turnstile> \<bottom>"
      thus "False"
        by (simp only: formula_semantics.simps(2))
    qed
    also have "(\<not> (setValuation S) \<Turnstile> \<bottom>) = (\<not> isModel (setValuation S) \<bottom>)"
      by (simp only: isModel_def)
    finally show "\<not> isModel (setValuation S) \<bottom>"
      by this
  qed
qed

lemma Hl2_2:
  assumes "Hintikka S"
  shows "(\<bottom> \<in> S \<longrightarrow> isModel (setValuation S) \<bottom>)
           \<and> (\<^bold>\<not> \<bottom> \<in> S \<longrightarrow> (\<not> (isModel (setValuation S) \<bottom>)))"
  by (simp add: Hintikka_l1 assms isModel_def)

lemma
  assumes "Hintikka S"
          "\<And>F. (F \<in> S \<longrightarrow> isModel (setValuation S) F) \<and>
         (\<^bold>\<not> F \<in> S \<longrightarrow> \<not> isModel (setValuation S) F)"
  shows "\<And>F. (\<^bold>\<not> F \<in> S \<longrightarrow> isModel (setValuation S) (\<^bold>\<not> F)) \<and>
         (\<^bold>\<not> (\<^bold>\<not> F) \<in> S \<longrightarrow> \<not> isModel (setValuation S) (\<^bold>\<not> F))"
proof (rule conjI) 
  show "\<And>F. \<^bold>\<not> F \<in> S \<longrightarrow> isModel (setValuation S) (\<^bold>\<not> F)"
  proof 
    fix F
    assume "\<^bold>\<not> F \<in> S"
    have "\<^bold>\<not> F \<in> S \<longrightarrow> \<not> isModel (setValuation S) F"
      using assms(2) by (rule conjunct2)
    then have "\<not> isModel (setValuation S) F"
      using  \<open>\<^bold>\<not> F \<in> S\<close> by (rule mp)
    also have "(\<not> isModel (setValuation S) F) = (\<not> (setValuation S) \<Turnstile> F)"
      by (simp only: isModel_def)
    also have "\<dots> = setValuation S \<Turnstile> (\<^bold>\<not> F)"
      by (simp only: formula_semantics.simps(3))
    also have "\<dots> = isModel (setValuation S) (\<^bold>\<not> F)"
      by (simp only: isModel_def)
    finally show "isModel (setValuation S) (\<^bold>\<not> F)"
      by this
  qed
next
  show "\<And>F. \<^bold>\<not> (\<^bold>\<not> F) \<in> S \<longrightarrow> \<not> isModel (setValuation S) (\<^bold>\<not> F)"
  proof
    fix F
    assume "\<^bold>\<not> (\<^bold>\<not> F) \<in> S"
    have "\<^bold>\<not> (\<^bold>\<not> F) \<in> S \<longrightarrow> F \<in> S" 
      using assms(1) by (rule Hintikka_l6)
    then have "F \<in> S"
      using \<open>\<^bold>\<not> (\<^bold>\<not> F) \<in> S\<close> by (rule mp)
    have "F \<in> S \<longrightarrow> isModel (setValuation S) F" 
      using assms(2) by (rule conjunct1)
    then have "isModel (setValuation S) F"
      using \<open>F \<in> S\<close> by (rule mp)
    then have "(\<not> (\<not> isModel (setValuation S) F))"
      by (rule contrapos_pn)
    also have "(\<not> (\<not> isModel (setValuation S) F)) = 
        (\<not> (\<not> (setValuation S) \<Turnstile> F))"
      by (simp only: isModel_def)
    also have "\<dots> = (\<not> (setValuation S) \<Turnstile> (\<^bold>\<not> F))"
      by (simp only: formula_semantics.simps(3))
    also have "\<dots> = (\<not> isModel (setValuation S) (\<^bold>\<not> F))"
      by (simp only: isModel_def)
    finally show "\<not> isModel (setValuation S) (\<^bold>\<not> F)"
      by this
  qed
qed

lemma Hl2_3:
  assumes "Hintikka S"
  shows " \<And>F. (F \<in> S \<longrightarrow> isModel (setValuation S) F) \<and>
         (\<^bold>\<not> F \<in> S \<longrightarrow> \<not> isModel (setValuation S) F) \<Longrightarrow>
         (\<^bold>\<not> F \<in> S \<longrightarrow> isModel (setValuation S) (\<^bold>\<not> F)) \<and>
         (\<^bold>\<not> (\<^bold>\<not> F) \<in> S \<longrightarrow> \<not> isModel (setValuation S) (\<^bold>\<not> F))"
  using Hintikka_l6 assms isModel_def formula_semantics.simps(3) by blast

lemma
  assumes "Hintikka S"
          "\<And>F1. (F1 \<in> S \<longrightarrow> isModel (setValuation S) F1) \<and>
           (\<^bold>\<not> F1 \<in> S \<longrightarrow> \<not> isModel (setValuation S) F1)" 
          "\<And>F2. (F2 \<in> S \<longrightarrow> isModel (setValuation S) F2) \<and>
           (\<^bold>\<not> F2 \<in> S \<longrightarrow> \<not> isModel (setValuation S) F2)"
  shows "\<And>F1 F2. (F1 \<^bold>\<and> F2 \<in> S \<longrightarrow> isModel (setValuation S) (F1 \<^bold>\<and> F2)) \<and>
       (\<^bold>\<not> (F1 \<^bold>\<and> F2) \<in> S \<longrightarrow> \<not> isModel (setValuation S) (F1 \<^bold>\<and> F2))"
proof (rule conjI)
  show "\<And>F1 F2. F1 \<^bold>\<and> F2 \<in> S \<longrightarrow> isModel (setValuation S) (F1 \<^bold>\<and> F2)"
  proof 
    fix F1 F2
    assume "F1 \<^bold>\<and> F2 \<in> S"
    have "F1 \<^bold>\<and> F2 \<in> S \<longrightarrow> F1 \<in> S \<and> F2 \<in> S"
      using assms(1) by (rule Hintikka_l3)
    then have C:"F1 \<in> S \<and> F2 \<in> S"
      using \<open>F1 \<^bold>\<and> F2 \<in> S\<close> by (rule mp)
    then have "F1 \<in> S" 
      by (rule conjunct1)
    have "F1 \<in> S \<longrightarrow> isModel (setValuation S) F1"
      using assms(2) by (rule conjunct1)
    then have "isModel (setValuation S) F1"
      using \<open>F1 \<in> S\<close> by (rule mp)
    then have I1:"(setValuation S) \<Turnstile> F1"
      by (simp only: isModel_def)
    have "F2 \<in> S"
      using C by (rule conjunct2)
    have "F2 \<in> S \<longrightarrow> isModel (setValuation S) F2"
      using assms(3) by (rule conjunct1)
    then have "isModel (setValuation S) F2"
      using \<open>F2 \<in> S\<close> by (rule mp)
    then have I2:"(setValuation S) \<Turnstile> F2"
      by (simp only: isModel_def) 
    have "((setValuation S) \<Turnstile> F1) \<and> ((setValuation S) \<Turnstile> F2)"
      using I1 I2 by (rule conjI)
    then have "(setValuation S) \<Turnstile> (F1 \<^bold>\<and> F2)"
      by (simp only: formula_semantics.simps(4))
    thus "isModel (setValuation S) (F1 \<^bold>\<and> F2)"
      by (simp only: isModel_def) 
  qed
next
  show "\<And>F1 F2. \<^bold>\<not> (F1 \<^bold>\<and> F2) \<in> S \<longrightarrow> \<not> isModel (setValuation S) (F1 \<^bold>\<and> F2)"
  proof
    fix F1 F2
    assume "\<^bold>\<not> (F1 \<^bold>\<and> F2) \<in> S"
    have "\<^bold>\<not> (F1 \<^bold>\<and> F2) \<in> S \<longrightarrow> \<^bold>\<not> F1 \<in> S \<or> \<^bold>\<not> F2 \<in> S"
      using assms(1) by (rule Hintikka_l7)
    then have "\<^bold>\<not> F1 \<in> S \<or> \<^bold>\<not> F2 \<in> S"
      using \<open>\<^bold>\<not> (F1 \<^bold>\<and> F2) \<in> S\<close> by (rule mp)
    then show "\<not> isModel (setValuation S) (F1 \<^bold>\<and> F2)"
    proof (rule disjE)
      assume "\<^bold>\<not> F1 \<in> S"
      have "\<^bold>\<not> F1 \<in> S \<longrightarrow> \<not> isModel (setValuation S) F1"
        using assms(2) by (rule conjunct2)
      then have "\<not> isModel (setValuation S) F1"
        using \<open>\<^bold>\<not> F1 \<in> S\<close> by (rule mp)
      also have "(\<not> isModel (setValuation S) F1) = (\<not> (setValuation S) \<Turnstile> F1)"
        by (simp only: isModel_def)
      finally have "\<not> (setValuation S) \<Turnstile> F1"
        by this
      then have "\<not> ((setValuation S) \<Turnstile> F1 \<and> (setValuation S) \<Turnstile> F2)" 
        by (rule notConj1)
      also have "(\<not> ((setValuation S) \<Turnstile> F1 \<and> (setValuation S) \<Turnstile> F2)) = 
          (\<not> ((setValuation S) \<Turnstile> F1 \<^bold>\<and> F2))"
        by (simp only: formula_semantics.simps(4))
      also have "\<dots> = (\<not> isModel (setValuation S) (F1 \<^bold>\<and> F2))"
        by (simp only: isModel_def)
      finally show "(\<not> isModel (setValuation S) (F1 \<^bold>\<and> F2))"
        by this
    next
      assume "\<^bold>\<not> F2 \<in> S"
      have "\<^bold>\<not> F2 \<in> S \<longrightarrow> \<not> isModel (setValuation S) F2"
        using assms(3) by (rule conjunct2)
      then have "\<not> isModel (setValuation S) F2"
        using \<open>\<^bold>\<not> F2 \<in> S\<close> by (rule mp)
      also have "(\<not> isModel (setValuation S) F2) = (\<not> (setValuation S) \<Turnstile> F2)"
        by (simp only: isModel_def)
      finally have "\<not> (setValuation S) \<Turnstile> F2"
        by this
      then have "\<not> ((setValuation S) \<Turnstile> F1 \<and> (setValuation S) \<Turnstile> F2)" 
        by (rule notConj2)
      also have "(\<not> ((setValuation S) \<Turnstile> F1 \<and> (setValuation S) \<Turnstile> F2)) = 
          (\<not> ((setValuation S) \<Turnstile> (F1 \<^bold>\<and> F2)))"
        by (simp only: formula_semantics.simps(4))
      also have "\<dots> = (\<not> isModel (setValuation S) (F1 \<^bold>\<and> F2))"
        by (simp only: isModel_def)
      finally show "\<not> isModel (setValuation S) (F1 \<^bold>\<and> F2)"
        by this
    qed
  qed
qed

lemma Hl2_4:
  assumes "Hintikka S"
  shows "\<And>F1 F2.
       (F1 \<in> S \<longrightarrow> isModel (setValuation S) F1) \<and>
       (\<^bold>\<not> F1 \<in> S \<longrightarrow> \<not> isModel (setValuation S) F1) \<Longrightarrow>
       (F2 \<in> S \<longrightarrow> isModel (setValuation S) F2) \<and>
       (\<^bold>\<not> F2 \<in> S \<longrightarrow> \<not> isModel (setValuation S) F2) \<Longrightarrow>
       (F1 \<^bold>\<and> F2 \<in> S \<longrightarrow> isModel (setValuation S) (F1 \<^bold>\<and> F2)) \<and>
       (\<^bold>\<not> (F1 \<^bold>\<and> F2) \<in> S \<longrightarrow> \<not> isModel (setValuation S) (F1 \<^bold>\<and> F2))"
  by (meson Hintikka_l3 Hintikka_l7 assms isModel_def formula_semantics.simps(4))

lemma
  assumes "Hintikka S"
          "\<And>F1. (F1 \<in> S \<longrightarrow> isModel (setValuation S) F1) \<and>
           (\<^bold>\<not> F1 \<in> S \<longrightarrow> \<not> isModel (setValuation S) F1)" 
          "\<And>F2. (F2 \<in> S \<longrightarrow> isModel (setValuation S) F2) \<and>
           (\<^bold>\<not> F2 \<in> S \<longrightarrow> \<not> isModel (setValuation S) F2)"
  shows "\<And>F1 F2. (F1 \<^bold>\<or> F2 \<in> S \<longrightarrow> isModel (setValuation S) (F1 \<^bold>\<or> F2)) 
  \<and> (\<^bold>\<not> (F1 \<^bold>\<or> F2) \<in> S \<longrightarrow> \<not> isModel (setValuation S) (F1 \<^bold>\<or> F2))"
proof (rule conjI)
  show "\<And> F1 F2. F1 \<^bold>\<or> F2 \<in> S \<longrightarrow> isModel (setValuation S) (F1 \<^bold>\<or> F2)"
  proof
    fix F1 F2
    assume "F1 \<^bold>\<or> F2 \<in> S"
    have "F1 \<^bold>\<or> F2 \<in> S \<longrightarrow> F1 \<in> S \<or> F2 \<in> S"
      using assms(1) by (rule Hintikka_l4)
    then have "F1 \<in> S \<or> F2 \<in> S"
      using \<open>F1 \<^bold>\<or> F2 \<in> S\<close> by (rule mp)
    then show "isModel (setValuation S) (F1 \<^bold>\<or> F2)"
    proof (rule disjE)
      assume "F1 \<in> S"
      have "F1 \<in> S \<longrightarrow> isModel (setValuation S) F1"
        using assms(2) by (rule conjunct1)
      then have "isModel (setValuation S) F1" 
        using \<open>F1 \<in> S\<close> by (rule mp)
      then have "(setValuation S) \<Turnstile> F1"
        by (simp only: isModel_def)
      then have "(setValuation S) \<Turnstile> F1 \<or> (setValuation S) \<Turnstile> F2"
        by (rule disjI1)
      then have "(setValuation S) \<Turnstile> (F1 \<^bold>\<or> F2)"
        by (simp only: formula_semantics.simps(5))
      thus "isModel (setValuation S) (F1 \<^bold>\<or> F2)"
        by (simp only: isModel_def)
    next
      assume "F2 \<in> S"
      have "F2 \<in> S \<longrightarrow> isModel (setValuation S) F2"
        using assms(3) by (rule conjunct1)
      then have "isModel (setValuation S) F2" 
        using \<open>F2 \<in> S\<close> by (rule mp)
      then have "(setValuation S) \<Turnstile> F2"
        by (simp only: isModel_def)
      then have "(setValuation S) \<Turnstile> F1 \<or> (setValuation S) \<Turnstile> F2"
        by (rule disjI2)
      then have "(setValuation S) \<Turnstile> (F1 \<^bold>\<or> F2)"
        by (simp only: formula_semantics.simps(5))
      thus "isModel (setValuation S) (F1 \<^bold>\<or> F2)"
        by (simp only: isModel_def)
    qed
  qed
next
  show "\<And>F1 F2. \<^bold>\<not> (F1 \<^bold>\<or> F2) \<in> S \<longrightarrow> \<not> isModel (setValuation S) (F1 \<^bold>\<or> F2)"
  proof (rule impI)
    fix F1 F2
    assume "\<^bold>\<not> (F1 \<^bold>\<or> F2) \<in> S"
    have "\<^bold>\<not> (F1 \<^bold>\<or> F2) \<in> S \<longrightarrow> \<^bold>\<not> F1 \<in> S \<and> \<^bold>\<not> F2 \<in> S"
      using assms(1) by (rule Hintikka_l8)
    then have C:"\<^bold>\<not> F1 \<in> S \<and> \<^bold>\<not> F2 \<in> S"
      using \<open>\<^bold>\<not> (F1 \<^bold>\<or> F2) \<in> S\<close> by (rule mp)
    then have "\<^bold>\<not> F1 \<in> S"
      by (rule conjunct1)
    have "\<^bold>\<not> F1 \<in> S \<longrightarrow> \<not> isModel (setValuation S) F1"
      using assms(2) by (rule conjunct2)
    then have "\<not> isModel (setValuation S) F1"
      using \<open>\<^bold>\<not> F1 \<in> S\<close> by (rule mp)
    also have "(\<not> isModel (setValuation S) F1) = (\<not> (setValuation S) \<Turnstile> F1)"
      by (simp only: isModel_def)
    finally have D1:"\<not> (setValuation S) \<Turnstile> F1"
      by this
    have "\<^bold>\<not> F2 \<in> S"
      using C by (rule conjunct2)
    have "\<^bold>\<not> F2 \<in> S \<longrightarrow> \<not> isModel (setValuation S) F2"
      using assms(3) by (rule conjunct2)
    then have "\<not> isModel (setValuation S) F2"
      using \<open>\<^bold>\<not> F2 \<in> S\<close> by (rule mp)
    also have "(\<not> isModel (setValuation S) F2) = (\<not> (setValuation S) \<Turnstile> F2)"
      by (simp only: isModel_def)
    finally have D2:"\<not> (setValuation S) \<Turnstile> F2"
      by this
    have "\<not> ((setValuation S) \<Turnstile> F1 \<or> (setValuation S) \<Turnstile> F2)"
      using D1 D2 by (rule notDisj)
    also have "(\<not> ((setValuation S) \<Turnstile> F1 \<or> (setValuation S) \<Turnstile> F2)) = 
          (\<not> (setValuation S) \<Turnstile> (F1 \<^bold>\<or> F2))"
      by (simp only: formula_semantics.simps(5))
    also have "\<dots> = (\<not> isModel (setValuation S) (F1 \<^bold>\<or> F2))"
      by (simp only: isModel_def)
    finally show "\<not> isModel (setValuation S) (F1 \<^bold>\<or> F2)"
      by this
  qed
qed


lemma Hl2_5:
  assumes "Hintikka S"
  shows "\<And>F1 F2.
       (F1 \<in> S \<longrightarrow> isModel (setValuation S) F1) \<and>
       (\<^bold>\<not> F1 \<in> S \<longrightarrow> \<not> isModel (setValuation S) F1) \<Longrightarrow>
       (F2 \<in> S \<longrightarrow> isModel (setValuation S) F2) \<and>
       (\<^bold>\<not> F2 \<in> S \<longrightarrow> \<not> isModel (setValuation S) F2) \<Longrightarrow>
       (F1 \<^bold>\<or> F2 \<in> S \<longrightarrow> isModel (setValuation S) (F1 \<^bold>\<or> F2)) \<and>
       (\<^bold>\<not> (F1 \<^bold>\<or> F2) \<in> S \<longrightarrow> \<not> isModel (setValuation S) (F1 \<^bold>\<or> F2))"
  by (smt Hintikka_def assms isModel_def formula_semantics.simps(5))

lemma
  assumes "Hintikka S"
          "\<And>F1. (F1 \<in> S \<longrightarrow> isModel (setValuation S) F1) \<and>
           (\<^bold>\<not> F1 \<in> S \<longrightarrow> \<not> isModel (setValuation S) F1)" 
          "\<And>F2. (F2 \<in> S \<longrightarrow> isModel (setValuation S) F2) \<and>
           (\<^bold>\<not> F2 \<in> S \<longrightarrow> \<not> isModel (setValuation S) F2)"
  shows "\<And>F1 F2. (F1 \<^bold>\<rightarrow> F2 \<in> S \<longrightarrow> isModel (setValuation S) (F1 \<^bold>\<rightarrow> F2)) 
      \<and> (\<^bold>\<not> (F1 \<^bold>\<rightarrow> F2) \<in> S \<longrightarrow> \<not> isModel (setValuation S) (F1 \<^bold>\<rightarrow> F2))"
proof (rule conjI)
  show "\<And>F1 F2. F1 \<^bold>\<rightarrow> F2 \<in> S \<longrightarrow> isModel (setValuation S) (F1 \<^bold>\<rightarrow> F2)"
  proof (rule impI)
    fix F1 F2
    assume "F1 \<^bold>\<rightarrow> F2 \<in> S"
    have "F1 \<^bold>\<rightarrow> F2 \<in> S \<longrightarrow> \<^bold>\<not> F1 \<in> S \<or> F2 \<in> S"
      using assms(1) by (rule Hintikka_l5)
    then have "\<^bold>\<not> F1 \<in> S \<or> F2 \<in> S"
      using \<open>F1 \<^bold>\<rightarrow> F2 \<in> S\<close> by (rule mp)
    then show "isModel (setValuation S) (F1 \<^bold>\<rightarrow> F2)"
    proof (rule disjE)
      assume "\<^bold>\<not> F1 \<in> S"
      have "\<^bold>\<not> F1 \<in> S \<longrightarrow> \<not> isModel (setValuation S) F1"
        using assms(2) by (rule conjunct2)
      then have "\<not> isModel (setValuation S) F1"
        using \<open>\<^bold>\<not> F1 \<in> S\<close> by (rule mp)
      also have "(\<not> isModel (setValuation S) F1) = (\<not> (setValuation S) \<Turnstile> F1)"
        by (simp only: isModel_def)
      finally have "\<not> (setValuation S) \<Turnstile> F1"
        by this
      have "(setValuation S) \<Turnstile> F1 \<longrightarrow> (setValuation S) \<Turnstile> F2"
      proof (rule impI)
        assume "(setValuation S) \<Turnstile> F1"
        show "(setValuation S) \<Turnstile> F2"
          using \<open>\<not> (setValuation S) \<Turnstile> F1\<close> \<open>(setValuation S) \<Turnstile> F1\<close> by (rule notE) 
      qed
      then have "(setValuation S) \<Turnstile> (F1 \<^bold>\<rightarrow> F2)"
        by (simp only: formula_semantics.simps(6))
      thus ?thesis
        by (simp only: isModel_def)
    next
      assume "F2 \<in> S"
      have "F2 \<in> S \<longrightarrow> isModel (setValuation S) F2"
        using assms(3) by (rule conjunct1)
      then have "isModel (setValuation S) F2"
        using \<open>F2 \<in> S\<close> by (rule mp)
      then have "(setValuation S) \<Turnstile> F2"
        by (simp only: isModel_def)
      have "(setValuation S) \<Turnstile> F1 \<longrightarrow> (setValuation S) \<Turnstile> F2"
      proof (rule impI)
        assume "(setValuation S) \<Turnstile> F1"
        show "(setValuation S) \<Turnstile> F2"
          using \<open>(setValuation S) \<Turnstile> F2\<close> by this 
      qed
      then have "(setValuation S) \<Turnstile> (F1 \<^bold>\<rightarrow> F2)"
        by (simp only: formula_semantics.simps(6))
      thus ?thesis
        by (simp only: isModel_def)
    qed
  qed
next
  show "\<And>F1 F2. \<^bold>\<not> (F1 \<^bold>\<rightarrow> F2) \<in> S \<longrightarrow> \<not> isModel (setValuation S) (F1 \<^bold>\<rightarrow> F2)"
  proof (rule impI)
    fix F1 F2
    assume "\<^bold>\<not> (F1 \<^bold>\<rightarrow> F2) \<in> S"
    have "\<^bold>\<not> (F1 \<^bold>\<rightarrow> F2) \<in> S \<longrightarrow> F1 \<in> S \<and> \<^bold>\<not> F2 \<in> S"
      using assms(1) by (rule Hintikka_l9)
    then have C:"F1 \<in> S \<and> \<^bold>\<not> F2 \<in> S"
      using \<open>\<^bold>\<not> (F1 \<^bold>\<rightarrow> F2) \<in> S\<close> by (rule mp)
    then have "F1 \<in> S"
      by (rule conjunct1)
    have "F1 \<in> S \<longrightarrow> isModel (setValuation S) F1"
      using assms(2) by (rule conjunct1)
    then have "isModel (setValuation S) F1"
      using \<open>F1 \<in> S\<close> by (rule mp)
    then have "(setValuation S) \<Turnstile> F1"
      by (simp only: isModel_def)
    have "\<^bold>\<not> F2 \<in> S"
      using C by (rule conjunct2)
    have "\<^bold>\<not> F2 \<in> S \<longrightarrow> \<not> isModel (setValuation S) F2"
      using assms(3) by (rule conjunct2)
    then have "\<not> isModel (setValuation S) F2"
      using \<open>\<^bold>\<not> F2 \<in> S\<close> by (rule mp)
    also have "(\<not> isModel (setValuation S) F2) = (\<not> (setValuation S) \<Turnstile> F2)"
      by (simp only: isModel_def)
    finally have "\<not> (setValuation S) \<Turnstile> F2"
      by this
    have "\<not> ((setValuation S) \<Turnstile> F1 \<longrightarrow> (setValuation S) \<Turnstile> F2)"
    proof (rule notI)
      assume "(setValuation S) \<Turnstile> F1 \<longrightarrow> (setValuation S) \<Turnstile> F2"
      then have "(setValuation S) \<Turnstile> F2"
        using \<open>(setValuation S) \<Turnstile> F1\<close> by (rule mp)
      show "False" 
        using \<open>\<not> (setValuation S) \<Turnstile> F2\<close> \<open>(setValuation S) \<Turnstile> F2\<close> by (rule notE)
    qed
    also have "(\<not> ((setValuation S) \<Turnstile> F1 \<longrightarrow> (setValuation S) \<Turnstile> F2)) = 
        (\<not> (setValuation S) \<Turnstile> (F1 \<^bold>\<rightarrow> F2))"
      by (simp only: formula_semantics.simps(6))
    also have "\<dots> = (\<not> isModel (setValuation S) (F1 \<^bold>\<rightarrow> F2))"
      by (simp only: isModel_def)
    finally show "\<not> isModel (setValuation S) (F1 \<^bold>\<rightarrow> F2)"
      by this
  qed
qed

lemma Hl2_6:
  assumes "Hintikka S"
  shows " \<And>F1 F2.
       (F1 \<in> S \<longrightarrow> isModel (setValuation S) F1) \<and>
       (\<^bold>\<not> F1 \<in> S \<longrightarrow> \<not> isModel (setValuation S) F1) \<Longrightarrow>
       (F2 \<in> S \<longrightarrow> isModel (setValuation S) F2) \<and>
       (\<^bold>\<not> F2 \<in> S \<longrightarrow> \<not> isModel (setValuation S) F2) \<Longrightarrow>
       (F1 \<^bold>\<rightarrow> F2 \<in> S \<longrightarrow> isModel (setValuation S) (F1 \<^bold>\<rightarrow> F2)) \<and>
       (\<^bold>\<not> (F1 \<^bold>\<rightarrow> F2) \<in> S \<longrightarrow> \<not> isModel (setValuation S) (F1 \<^bold>\<rightarrow> F2))"
  by (meson Hintikka_l5 Hintikka_l9 assms isModel_def formula_semantics.simps(6))

lemma Hintikkas_lemma_l2:
  assumes "Hintikka S"
  shows "(F \<in> S \<longrightarrow> isModel (setValuation S) F)
           \<and> (\<^bold>\<not> F \<in> S \<longrightarrow> (\<not>(isModel (setValuation S) F)))"
proof (induct F)
  fix x
  show "(Atom x \<in> S \<longrightarrow> isModel (setValuation S) (Atom x)) \<and>
         (\<^bold>\<not> (Atom x) \<in> S \<longrightarrow> \<not> isModel (setValuation S) (Atom x))"
    using assms by (rule Hl2_1)
next
  show "(\<bottom> \<in> S \<longrightarrow> isModel (setValuation S) \<bottom>) \<and>
    (\<^bold>\<not> \<bottom> \<in> S \<longrightarrow> \<not> isModel (setValuation S) \<bottom>)" 
    using assms by (rule Hl2_2)
next
  fix F
  show "(F \<in> S \<longrightarrow> isModel (setValuation S) F) \<and>
         (\<^bold>\<not> F \<in> S \<longrightarrow> \<not> isModel (setValuation S) F) \<Longrightarrow>
         (\<^bold>\<not> F \<in> S \<longrightarrow> isModel (setValuation S) (\<^bold>\<not> F)) \<and>
         (\<^bold>\<not> (\<^bold>\<not> F) \<in> S \<longrightarrow> \<not> isModel (setValuation S) (\<^bold>\<not> F))"
    using assms by (rule Hl2_3)
next
  fix F1 F2
  show "(F1 \<in> S \<longrightarrow> isModel (setValuation S) F1) \<and>
       (\<^bold>\<not> F1 \<in> S \<longrightarrow> \<not> isModel (setValuation S) F1) \<Longrightarrow>
       (F2 \<in> S \<longrightarrow> isModel (setValuation S) F2) \<and>
       (\<^bold>\<not> F2 \<in> S \<longrightarrow> \<not> isModel (setValuation S) F2) \<Longrightarrow>
       (F1 \<^bold>\<and> F2 \<in> S \<longrightarrow> isModel (setValuation S) (F1 \<^bold>\<and> F2)) \<and>
       (\<^bold>\<not> (F1 \<^bold>\<and> F2) \<in> S \<longrightarrow> \<not> isModel (setValuation S) (F1 \<^bold>\<and> F2))"
    using assms by (rule Hl2_4)
next
  fix F1 F2
  show "(F1 \<in> S \<longrightarrow> isModel (setValuation S) F1) \<and>
       (\<^bold>\<not> F1 \<in> S \<longrightarrow> \<not> isModel (setValuation S) F1) \<Longrightarrow>
       (F2 \<in> S \<longrightarrow> isModel (setValuation S) F2) \<and>
       (\<^bold>\<not> F2 \<in> S \<longrightarrow> \<not> isModel (setValuation S) F2) \<Longrightarrow>
       (F1 \<^bold>\<or> F2 \<in> S \<longrightarrow> isModel (setValuation S) (F1 \<^bold>\<or> F2)) \<and>
       (\<^bold>\<not> (F1 \<^bold>\<or> F2) \<in> S \<longrightarrow> \<not> isModel (setValuation S) (F1 \<^bold>\<or> F2))"
    using assms by (rule Hl2_5)
next
  fix F1 F2
  show "(F1 \<in> S \<longrightarrow> isModel (setValuation S) F1) \<and>
       (\<^bold>\<not> F1 \<in> S \<longrightarrow> \<not> isModel (setValuation S) F1) \<Longrightarrow>
       (F2 \<in> S \<longrightarrow> isModel (setValuation S) F2) \<and>
       (\<^bold>\<not> F2 \<in> S \<longrightarrow> \<not> isModel (setValuation S) F2) \<Longrightarrow>
       (F1 \<^bold>\<rightarrow> F2 \<in> S \<longrightarrow> isModel (setValuation S) (F1 \<^bold>\<rightarrow> F2)) \<and>
       (\<^bold>\<not> (F1 \<^bold>\<rightarrow> F2) \<in> S \<longrightarrow> \<not> isModel (setValuation S) (F1 \<^bold>\<rightarrow> F2))"
    using assms by (rule Hl2_6)
qed

text \<open>Para concluir, demostremos el \<open>Lema de Hintikka\<close> empleando el
  resultado anterior.

  \begin{teorema}[Lema de Hintikka]
    Todo conjunto de Hintikka es satisfacible.
  \end{teorema}

  \begin{demostracion}
    Consideremos un conjunto de fórmulas \<open>S\<close> tal que sea un conjunto de 
    Hintikka. Queremos demostrar que \<open>S\<close> es satisfacible, es decir, que 
    tiene algún modelo. En otras palabras, debemos hallar una 
    interpretación que sea modelo de \<open>S\<close>.

    En primer lugar, probemos que la interpretación asociada a \<open>S\<close> es 
    modelo de \<open>S\<close>. Por definición de modelo de un conjunto, basta 
    comprobar que es modelo de toda fórmula perteneciente al mismo. 
    Fijada una fórmula cualquiera, hemos visto anteriormente que la 
    interpretación asociada a \<open>S\<close> es modelo de la fórmula si esta 
    pertenece al conjunto. Por tanto, dicha interpretación es, en 
    efecto, modelo de todas las fórmulas que pertenecen a \<open>S\<close>. Luego la 
    interpretación asociada a \<open>S\<close> es modelo de \<open>S\<close>.

    En conclusión, hemos hallado una interpretación que es modelo del
    conjunto. Por lo tanto, \<open>S\<close> es satisfacible, como se quería probar.
  \end{demostracion}

  Por su parte, la prueba detallada en Isabelle emplea el lema
  auxiliar \<open>Hintikka_model\<close>. Con él se demuestra la primera parte del 
  lema de Hintikka: dado un conjunto de Hintikka, la interpretación 
  asociada al conjunto es modelo del mismo.\<close>

lemma Hintikka_model:
  assumes "Hintikka S"
  shows "isModelSet (setValuation S) S"
proof -
  have "\<forall>F. (F \<in> S \<longrightarrow> isModel (setValuation S) F)"
  proof (rule allI)
    fix F
    have "(F \<in> S \<longrightarrow> isModel (setValuation S) F)
           \<and> (\<^bold>\<not> F \<in> S \<longrightarrow> (\<not>(isModel (setValuation S) F)))"
      using assms by (rule Hintikkas_lemma_l2)
    thus "F \<in> S \<longrightarrow> isModel (setValuation S) F"
      by (rule conjunct1)
  qed
  thus "isModelSet (setValuation S) S"
    by (simp only: modelSet)
qed 

text \<open>Finalmente, las pruebas detallada y automática del 
  \<open>Lema de Hintikka\<close> en Isabelle/HOL.\<close>

theorem
  assumes "Hintikka S"
  shows "sat S"
proof -
  have "isModelSet (setValuation S) S"
    using assms by (rule Hintikka_model)
  then have "\<exists>\<A>. isModelSet \<A> S"
    by (simp only: exI)
  thus "sat S" 
    by (simp only: satAlt)
qed

theorem Hintikkaslemma:
  assumes "Hintikka S"
  shows "sat S"
  using Hintikka_model assms satAlt by blast

(*<*)
end
(*>*) 