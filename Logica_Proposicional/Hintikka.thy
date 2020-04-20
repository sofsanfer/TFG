(*<*) 
theory Hintikka
  imports 
    Sintaxis
    Semantica
begin
(*>*)

section \<open>Conjuntos de Hintikka y propiedades\\ básicas\<close>

text \<open>En esta sección presentaremos un tipo de conjuntos de fórmulas:
  los conjuntos de Hintikka. Probaremos finalmente que todo conjunto 
  de Hintikka es satisfacible.

  \begin{definicion}
  Se llama \<open>conjunto de Hintikka\<close> a todo conjunto de fórmulas que
  verifica las siguientes condiciones para todo par de fórmulas
  \<open>F\<close> y \<open>G\<close>:
    \begin{enumerate}
      \item \<open>\<bottom>\<close> no pertenece al conjunto.
      \item Si una fórmula atómica \<open>p\<close> pertenece al conjunto, entonces 
        \<open>\<not> p\<close> no pertenece al conjunto.
      \item Si \<open>F \<and> G\<close> pertenece al conjunto, entonces \<open>F\<close> y \<open>G\<close> 
        pertenecen al conjunto.
      \item Si \<open>F \<or> G\<close> pertenece al conjunto, entonces \<open>F\<close> pertenece al 
        conjunto o \<open>G\<close> pertenece al conjunto.
      \item Si \<open>F \<rightarrow> G\<close> pertenece al conjunto, entonces \<open>\<not> F\<close> pertenece 
        al conjunto o \<open>G\<close> pertenece al conjunto.
      \item Si \<open>\<not>(\<not> F)\<close> pertenece al conjunto, entonces \<open>F\<close> pertenece 
        al conjunto.
      \item Si \<open>\<not>(F \<and> G)\<close> pertenece al conjunto, entonces \<open>\<not> F\<close> 
        pertenece al conjunto o\\ \<open>\<not> G\<close> pertenece al conjunto.
      \item Si \<open>\<not>(F \<or> G)\<close> pertenece al conjunto, entonces \<open>\<not> F\<close> y \<open>\<not> G\<close> 
        pertenecen al conjunto.
      \item Si \<open>\<not>(F \<rightarrow> G)\<close> pertenece al conjunto, entonces \<open>F\<close> y \<open>\<not> G\<close> 
        pertenecen al conjunto.
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

text \<open>Mostremos a continuación un ejemplo de conjunto de fórmulas que
  sea de Hintikka.\<close>

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

text \<open>A continuación vamos a presentar una serie de lemas auxiliares
  derivados de la definición de conjunto de Hintikka que nos facilitarán
  posteriormente las demostraciones en Isabelle/HOL.

  El primer lema expresa que, dado un conjunto de Hintikka,
  dicho conjunto verifica las nueve condiciones de la definición 
  anterior. Se trata de un resultado que posteriormente nos ayudará
  a probar los nueve siguientes lemas auxiliares.\<close>

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
  condición de la definición de conjunto de Hintikka. De este modo,
  dado un conjunto de Hintikka, entonces cumple por separado cada 
  condición señalada anteriormente. Veamos las demostraciones detalladas 
  y automáticas en\\ Isabelle/HOL de cada lema auxiliar.\<close>

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
  then have "(\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
  \<and>(\<forall>F G. F \<^bold>\<and> G \<in> S \<longrightarrow> F \<in> S \<and> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<or> G \<in> S \<longrightarrow> F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> \<^bold>\<not>F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S)"
    by (rule conjunct2)
  then have "(\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)"
    by (rule conjunct1)
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
    by (iprover intro: conjunct2 conjunct1) 
  then have "\<forall> G. F \<^bold>\<and> G \<in> S \<longrightarrow> F \<in> S \<and> G \<in> S"
    by (rule allE)
  then have "F \<^bold>\<and> G \<in> S \<longrightarrow> F \<in> S \<and> G \<in> S"
    by (rule allE)
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
    by (iprover intro: conjunct2 conjunct1)
  then have "\<forall>G. F \<^bold>\<or> G \<in> S \<longrightarrow> F \<in> S \<or> G \<in> S"
    by (rule allE)
  then have "F \<^bold>\<or> G \<in> S \<longrightarrow> F \<in> S \<or> G \<in> S"
    by (rule allE)
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
    by (iprover intro: conjunct2 conjunct1)
  then have "\<forall>G. F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> \<^bold>\<not>F \<in> S \<or> G \<in> S"
    by (rule allE)
  then have "F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> \<^bold>\<not>F \<in> S \<or> G \<in> S"
    by (rule allE)
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
    by (iprover intro: conjunct2 conjunct1)
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
    by (iprover intro: conjunct2 conjunct1)
  then have "\<forall>G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S"
    by (rule allE)
  then have "\<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S"
    by (rule allE)
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
    by (iprover intro: conjunct2 conjunct1)
  then have "\<forall>G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S"
    by (rule allE)
  then have "\<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S"
    by (rule allE)
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
    by (iprover intro: conjunct2)
  then have "\<forall>G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S"
    by (rule allE)
  then have "\<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S"
    by (rule allE)
  thus "F \<in> S \<and> \<^bold>\<not> G \<in> S"
    using H by (rule mp)
qed

lemma Hintikka_l9: 
 "Hintikka S \<Longrightarrow> \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S"
  by (smt Hintikka_def)

text \<open>\comentario{Explicar iprover intro.}\<close>

text \<open>Finalmente, veamos un resultado derivado de las condiciones
  exigidas a los conjuntos de Hintikka.

  \begin{lema}
    Sea un conjunto de Hintikka y \<open>F\<close> una fórmula cualquiera.
    Si \<open>\<not> F\<close> pertenece al conjunto, entonces \<open>F\<close> no pertenece al
    conjunto.
  \end{lema}

  Su formalización en Isabelle es la siguiente.\<close>

lemma "Hintikka S \<Longrightarrow> (\<^bold>\<not> F \<in> S \<longrightarrow> F \<notin> S)"
  oops

text \<open>Para la demostración del siguiente lema, vamos a utilizar las
  reglas lógicas \<open>modus tollens\<close> e \<open>introducción a la doble negación\<close>. 

  \begin{teorema}[Modus tollens]
   Si un enunciado implica otro y tenemos que el segundo es falso, 
   entonces el primero es también falso.
  \end{teorema}

  Esta regla no está definida en Isabelle, de modo que las vamos a 
  introducir a continuación como lema auxiliar. Además, mostraremos
  su prueba detallada usando otras reglas sí definidas en Isabelle/HOL.\<close>

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

text \<open>Por otro lado, veamos la \<open>introducción de la doble negación\<close>.

  \begin{teorema}[Introducción de la doble negación]
   Si un enunciado es verdadero, entonces no es cierto que ese
   enunciado no sea verdadero.
  \end{teorema}

  En Isabelle se formaliza y demuestra de la siguiente manera.\<close>

lemma notnotI: "A \<Longrightarrow> \<not>\<not> A"
  by (rule contrapos_pn)

text \<open>En este caso, la regla \<open>contrapos_pn\<close> de la teoría
  \href{http://bit.ly/38iFKlA}{HOL.thy} prueba el resultado de manera
  directa.

  \begin{itemize}
    \item[] @{thm[mode=Rule] contrapos_pn[no_vars]} 
      \hfill (@{text contrapos_pn})
  \end{itemize}

  Es fácil observar que \<open>notnotI\<close> se trata de un caso particular de
  \<open>contrapos_pn\<close> en el que \<open>Q \<equiv> A\<close> y \<open>P \<equiv> \<not> A\<close>. 

  Una vez realizadas las aclaraciones anteriores, procedamos con la
  demostración del lema.

  \begin{demostracion}
    La prueba se realiza por inducción sobre la estructura de las 
    fórmulas proposicionales. Veamos los distintos casos.

    En primer lugar, consideremos una fórmula atómica cualquiera \<open>p\<close> y 
    \<open>S\<close> un conjunto de Hintikka. Queremos probar que si \<open>\<not> p\<close> pertenece 
    al conjunto, entonces \<open>p\<close> no pertenece al conjunto. Supongamos, 
    pues, que \<open>\<not> p\<close> pertenece a \<open>S\<close>. Entonces, introduciendo la doble 
    negación, obtenemos la negación de \<open>\<not> p\<close> no pertenece a \<open>S\<close>. Por 
    otro lado, como hemos supuesto que \<open>S\<close> es un conjunto de Hintikka, 
    verifica la segunda condición para \<open>p\<close>: si \<open>p\<close> pertenece a \<open>S\<close>,
    entonces \<open>\<not> p\<close> no pertenece a \<open>S\<close>. Como anteriormente habíamos
    supuesto la negación de \<open>\<not> p\<close> no pertenece a \<open>S\<close>, por la regla
    lógica de \<open>modus tollens\<close>, se tiene por tanto que \<open>p\<close> no pertenece
    al conjunto.

    Sea la fórmula \<open>\<bottom>\<close> y \<open>S\<close> un conjunto de Hintikka. Probemos que si\\
    \<open>\<not> \<bottom>\<close> pertenece a \<open>S\<close>, entonces \<open>\<bottom>\<close> no pertenece a \<open>S\<close>. Para ello,
    suponemos inicialmente que \<open>\<not> \<bottom>\<close> pertenece a \<open>S\<close>. Como \<open>S\<close> es un 
    conjunto de Hintikka por hipótesis, sabemos que verifica la primera
    condición de la definición, de modo que \<open>\<bottom>\<close> no pertenece a \<open>S\<close>, 
    como queríamos demostrar.

    Consideremos \<open>S\<close> un conjunto de Hintikka. Sea \<open>F\<close> una fórmula
    cualquiera tal que para todo conjunto de Hintikka verifica que si
    \<open>\<not> F\<close> pertenece al conjunto, entonces \<open>F\<close> no pertenece al conjunto.
    Vamos a probar que si \<open>\<not> (\<not> F)\<close> pertenece a \<open>S\<close>, entonces \<open>\<not> F\<close>
    no pertenece a \<open>S\<close>.
    Para ello, suponemos inicialmente que \<open>\<not> (\<not> F)\<close> pertenece a \<open>S\<close>. 
    Como \<open>S\<close> es un conjunto de Hintikka por hipótesis, tenemos que
    verifica la sexta condición de la definición para \<open>F\<close>: si \<open>\<not> (\<not> F)\<close>
    pertenece a \<open>S\<close>, entonces \<open>F\<close> pertenece a \<open>S\<close>. Por tanto, obtenemos
    de la primera suposición que \<open>F\<close> pertenece a \<open>S\<close>. Introduciendo la
    doble negación, es equivalente a la negación de \<open>F\<close> no pertenece a
    \<open>S\<close>. Por otra parte, al ser \<open>S\<close> un conjunto de Hintikka, por 
    hipótesis de inducción se verifica que si \<open>\<not> F\<close> pertenece a \<open>S\<close>, 
    entonces \<open>F\<close> no pertenece a \<open>S\<close>. Como anteriormente obtuvimos la
    negación de \<open>F\<close> no pertenece a \<open>S\<close>, por la regla lógica del \<open>modus
    tollens\<close>, llegamos finalmente a que \<open>\<not> F\<close> no pertenece a \<open>S\<close>.

    Sea \<open>S\<close> un conjunto de Hintikka. Consideremos la fórmula \<open>G\<close> tal
    que, para cualquier conjunto de Hintikka, si \<open>\<not> G\<close> pertenece al
    conjunto, entonces \<open>G\<close> no pertenece al conjunto. Sea también la
    fórmula \<open>H\<close> que verifica análogamente para cualquier conjunto de 
    Hintikka que, si \<open>\<not> H\<close> pertenece al conjunto, entonces \<open>H\<close> no 
    pertenece al conjunto. Queremos probar que si \<open>\<not> (G \<and> H)\<close> pertenece
    a \<open>S\<close>, entonces \<open>G \<and> H\<close> no pertenece a \<open>S\<close>.\\
    Para ello, suponemos inicialmente que \<open>\<not> (G \<and> H)\<close> pertenece a \<open>S\<close>.
    Como \<open>S\<close> es un conjunto de Hintikka, por la séptima condición de la 
    definición, tenemos que si \<open>\<not> (G \<and> H)\<close> pertenece a \<open>S\<close>, entonces 
    \<open>\<not> G\<close> pertenece a \<open>S\<close> o \<open>\<not> H\<close> pertenece \<open>S\<close>. Como habíamos supuesto 
    inicialmente que\\ \<open>\<not> (G \<and> H)\<close> pertenece a \<open>S\<close>, por la anterior 
    tenemos que \<open>\<not> G\<close> pertenece a \<open>S\<close> o \<open>\<not> H\<close> pertenece a \<open>S\<close>. De este
    modo, voy a probar que \<open>G \<and> H\<close> no pertenece a \<open>S\<close> por la
    eliminación de la disyunción anterior.\\
    En primer lugar, supongamos que \<open>\<not> G\<close> pertenece a \<open>S\<close>. Entonces,
    como \<open>S\<close> es un conjunto de Hintikka, por hipótesis de inducción 
    tenemos que, si\\ \<open>\<not> G\<close> pertenece a \<open>S\<close>, entonces \<open>G\<close> no pertenece 
    a \<open>S\<close>. Como habíamos supuesto que \<open>\<not> G\<close> pertenece a \<open>S\<close>, por lo
    anterior obtenemos que \<open>G\<close> no pertenece a \<open>S\<close>. Por propiedades de
    la conjunción, se observa fácilmente que si \<open>G\<close> no pertenece a
    \<open>S\<close>, entonces no es cierto que \<open>G\<close> y \<open>H\<close> pertenezcan ambas a \<open>S\<close>.
    Por otro lado, como \<open>S\<close> es un conjunto de Hintikka, cumple también 
    la condición tercera de la definición para \<open>G\<close> y \<open>H\<close>: si \<open>G \<and> H\<close>
    pertenece a \<open>S\<close>, entonces \<open>G\<close> y \<open>H\<close> pertenecen ambas a \<open>S\<close>. Como 
    anteriormente obtubimos que no es cierto que \<open>G\<close> y \<open>H\<close> pertenezcan
    a \<open>S\<close>, por la regla de \<open>modus tollens\<close> obtenemos finalmente que
    \<open>G \<and> H\<close> no pertenece a \<open>S\<close>.\\
    En segundo lugar, supongamos que \<open>\<not> H\<close> pertenece a \<open>S\<close>. Vamos a
    probar análogamente que \<open>G \<and> H\<close> no pertenece a \<open>S\<close>. Por hipótesis
    de inducción, como \<open>S\<close> es un conjunto de Hintikka, tenemos que si
    \<open>\<not> H\<close> pertenece a \<open>S\<close>, entonces \<open>H\<close> no pertenece a \<open>S\<close>. Como en
    este caso hemos supuesto que\\ \<open>\<not> H\<close> pertenece a \<open>S\<close>, por lo 
    anterior obtenemos que \<open>H\<close> no pertenece a \<open>S\<close>. Razonando igual que 
    en el caso anterior con respecto a la conjunción, como \<open>H\<close> no 
    pertenece a \<open>S\<close>, entonces no es cierto que \<open>G\<close> y \<open>H\<close> pertenezcan 
    ambas a \<open>S\<close>. Por otra parte, como \<open>S\<close> es un conjunto de Hintikka, 
    verifica la condición tercera de la definición para \<open>G\<close> y \<open>H\<close>: si 
    \<open>G \<and> H\<close> pertenece a \<open>S\<close>, entonces \<open>G\<close> y \<open>H\<close> pertenecen ambas a \<open>S\<close>. 
    Por lo tanto, como no es cierto que \<open>G\<close> y \<open>H\<close> pertenezcan ambas a 
    \<open>S\<close>, por la regla del \<open>modus tollens\<close> se demuestra finalmente que 
    \<open>G \<and> H\<close> no pertenece a \<open>S\<close>. 

    Sea el conjunto de Hintikka \<open>S\<close>. Consideremos la fórmula \<open>G\<close> tal
    que dado un conjunto de Hintikka cualquiera, si \<open>\<not> G\<close> pertenece a
    dicho conjunto, entonces \<open>G\<close> no pertenece a él. Del mismo modo se
    considera otra fórmula \<open>H\<close> verificando para cualquier conjunto de 
    Hintikka que, si \<open>\<not> H\<close> pertenece al conjunto, entonces \<open>H\<close> no 
    pertence a él. Queremos probar que si \<open>\<not> (G \<or> H)\<close> pertenece a \<open>S\<close>,
    entonces \<open>G \<or> H\<close> no pertenece a \<open>S\<close>.\\
    Supongamos inicialmente que \<open>\<not> (G \<or> H)\<close> pertence a \<open>S\<close>. Como \<open>S\<close>
    es un conjunto de Hintikka, en particular verifica la condición 
    octava de su definición: si \<open>\<not> (G \<or> H)\<close> pertence \<open>S\<close>, entonces 
    \<open>\<not> G\<close> y \<open>\<not> H\<close> están también en el conjunto. Luego, por la
    suposición inicial, obtenemos que tanto \<open>\<not> G\<close> como \<open>\<not> H\<close> están en 
    \<open>S\<close>. En particular, \<open>\<not> G\<close> está en \<open>S\<close>. Como \<open>S\<close> es conjunto de 
    Hintikka, por hipótesis de inducción tenemos que si \<open>\<not> G\<close> pertence
    a \<open>S\<close>, entonces \<open>G\<close> no pertenece al conjunto. Por tanto, como
    \<open>\<not> G\<close> está en \<open>S\<close>, obtenemos así que \<open>G\<close> no está en el conjunto.\\
    Por otra parte, \<open>\<not> H\<close> también está en \<open>S\<close> como vimos
    anteriormente. Al ser \<open>S\<close> un conjunto de Hintikka, aplicando la
    hipótesis de inducción tenemos que si \<open>\<not> H\<close> está en \<open>S\<close>, entonces
    \<open>H\<close> no pertenece al conjunto. Por tanto, tenemos así que \<open>H\<close> no 
    está en \<open>S\<close>.\\ Recopilando lo anterior, hemos llegado a que ni
    \<open>G\<close> ni \<open>H\<close> están en el conjunto. Es fácil observar que esto implica,
    en particular, que no es cierto que \<open>G\<close> esté en \<open>S\<close> o \<open>H\<close> esté en 
    \<open>S\<close>. De nuevo, al ser \<open>S\<close> conjunto de Hintikka, verifica la
    condición cuarta de la definición para \<open>G\<close> y \<open>H\<close>: si \<open>G \<or> H\<close> 
    pertenece a \<open>S\<close>, entonces \<open>G\<close> pertenece a \<open>S\<close> o \<open>H\<close> pertenece a
    \<open>S\<close>. Como deducimos de lo anterior que no es cierto que \<open>G\<close>
    pertenezca a \<open>S\<close> o \<open>H\<close> pertenezca a \<open>S\<close>, por la regla del 
    \<open>modus tollens\<close> obtenemos finalmente que \<open>G \<or> H\<close> no pertenece a \<open>S\<close>.

    Veamos el último caso de la estructura de las fórmulas.
    Consideremos análogamente un conjunto de Hintikka \<open>S\<close>. Sea también
    la fórmula \<open>G\<close> tal que dado cualquier conjunto de Hintikka, si \<open>\<not> G\<close>
    está en el conjunto, entonces \<open>G\<close> no lo está. Del mismo modo se 
    considera la fórmula \<open>H\<close> tal que para un conjunto de Hintikka
    cualquiera verifica análogamente que si \<open>\<not> H\<close> pertenece al
    conjunto, entonces \<open>H\<close> no pertenece a él. Vamos a probar que si
    \<open>\<not> (G \<longrightarrow> H)\<close> pertenece a \<open>S\<close>, entonces \<open>G \<longrightarrow> H\<close> no pertenece a 
    \<open>S\<close>.\\
    Para ello, como es habitual, suponemos inicialmente que 
    \<open>\<not> (G \<longrightarrow> H)\<close> está en \<open>S\<close>. Al ser \<open>S\<close> un conjunto de Hintikka, en 
    particular verifica la condición novena de su definición: si
    \<open>\<not> (G \<longrightarrow> H)\<close> pertenece a \<open>S\<close>, entonces \<open>G\<close> y \<open>\<not> H\<close> pertenecen 
    ambas a \<open>S\<close>. Luego tenemos que tanto \<open>G\<close> como \<open>\<not> H\<close> pertencen
    a \<open>S\<close>. En particular tenemos, por tanto, que \<open>G\<close> pertenece
    al conjunto. Introduciendo la doble negación, se deduce que no es 
    cierto que \<open>G\<close> no pertenezca a \<open>S\<close>. Como \<open>S\<close> es un conjunto de 
    Hintikka, por hipótesis de inducción se verifica que si \<open>\<not> G\<close> 
    pertence a \<open>S\<close>, entonces \<open>G\<close> no pertence a \<open>S\<close>. Como hemos deducido 
    anteriormente que no es cierto que \<open>G\<close> no pertenezca a \<open>S\<close>, 
    aplicando la regla del \<open>modus tollens\<close> obtenemos que \<open>\<not> G\<close> no 
    pertenece al conjunto.\\
    Por otro lado, anteriormente deducimos también que \<open>\<not> H\<close> está en
    \<open>S\<close>. Como \<open>S\<close> es de Hintikka, por hipótesis de inducción si \<open>\<not> H\<close>
    está en \<open>S\<close>, entonces \<open>H\<close> no lo está. Por tanto, obtenemos así que
    \<open>H\<close> no pertenece a \<open>S\<close>.\\ Recopilando lo obtenido anteriormente, 
    bajo las condiciones supuestas tenemos que ni \<open>\<not> G\<close> ni \<open>H\<close>
    pertenecen a \<open>S\<close>. Por lo tanto, es fácil observar que no es cierto
    que \<open>\<not> G\<close> pertenezca a \<open>S\<close> o \<open>H\<close> pertenezca a \<open>S\<close>. Como \<open>S\<close> es un
    conjunto de Hintikka, verifica en particular la quinta condición de
    su definición para \<open>G\<close> y \<open>H\<close>, de modo que si \<open>G \<longrightarrow> H\<close> está en \<open>S\<close>,
    entonces \<open>\<not> G\<close> está en \<open>S\<close> o \<open>H\<close> está en \<open>S\<close>. Finalmente, obtenemos
    de aquí que \<open>G \<longrightarrow> H\<close> no pertenece a \<open>S\<close> aplicando la regla del
    \<open>modus tollens\<close>.
  \end{demostracion}

  Como es habitual, demostremos ahora el resultado en Isabelle/HOL de
  manera detallada. Para facilitar dicha prueba, se hará cada caso de la
  estructura de fórmulas por separado.\<close>

lemma Hintikka_l10_atom: 
  assumes "Hintikka S" 
  shows "\<^bold>\<not> (Atom x) \<in> S \<longrightarrow> Atom x \<notin> S"
proof (rule impI)
  assume "\<^bold>\<not> (Atom x) \<in> S"
  then have "\<not> (\<^bold>\<not> (Atom x) \<notin> S)"
    by (rule notnotI)
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
    by (rule notnotI)
  have "\<^bold>\<not> F \<in> S \<longrightarrow> F \<notin> S"
    using assms by this
  thus "\<^bold>\<not> F \<notin> S"
    using \<open>\<not> (F \<notin> S)\<close> by (rule mt)
qed

text \<open>A continuación, los siguientes lemas auxiliares nos permitirán
  introducir la negación de una conjunción o disyunción de dos 
  predicados. Estos resultados nos facilitarán las pruebas de los casos 
  de conectivas binarias. Se observa que aparecen demostrados de 
  manera detallada en Isabelle.\<close>

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

text \<open>De este modo, comencemos las pruebas detalladas de las conectivas
  binarias. Una vez terminadas las demostraciones de cada caso por
  separado, se mostrará la prueba detallada del lema completo.\<close>

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
    by (rule notnotI)
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
  propiedades que se deducen de ella, veamos el resultado más importante
  sobre este tipo de conjuntos.

  \begin{teorema}[Lema de Hintikka]
    Todo conjunto de Hintikka es satisfacible.
  \end{teorema}

  Por definición, para probar que un conjunto es satisfacible, basta
  hallar una interpretación que sea modelo suyo. De este modo, dado
  un conjunto cualquiera definimos las siguientes interpretaciones
  asociadas.

  \begin{definicion}
    Sea \<open>S\<close> un conjunto de fórmulas. Se define la \<open>interpretación 
    asociada a S\<close> como aquella que, dada una variable proposicional,
    devuelve \<open>Verdadero\<close> si su correspondiente fórmula atómica pertence 
    al conjunto, y \<open>Falso\<close> en caso contrario.
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

text \<open>Previamente a la demostración del \<open>Lema de Hintikka\<close> y con el fin
  de facilitarla, introduciremos el siguiente resultado.

  \begin{lema}
    La interpretación asociada a un conjunto de Hintikka es modelo de
    toda fórmula perteneciente al conjunto. Además, dicha interpretación
    no es modelo de las fórmulas cuya negación pertenece al conjunto.
  \end{lema}

  Su formalización en Isabelle es la siguiente.\<close>

lemma
  assumes "Hintikka S"
  shows "(F \<in> S \<longrightarrow> isModel (setValuation S) F)
           \<and> (\<^bold>\<not> F \<in> S \<longrightarrow> (\<not>(isModel (setValuation S) F)))"
  oops

text \<open>Procedamos a la demostración del resultado.
  \begin{demostracion}
    El lema se prueba mediante inducción en la estructura de las
    fórmulas. Como es habitual, se distinguen los siguientes casos.

    En primer lugar, 
  \end{demostracion}\<close>

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
      by (rule notnotI)
    also have "(\<not> (\<not> isModel (setValuation S) F)) = (\<not> (\<not> (setValuation S) \<Turnstile> F))"
      by (simp only: isModel_def)
    also have "\<dots> = (\<not> (setValuation S) \<Turnstile> (\<^bold>\<not> F))"
      by (simp only: formula_semantics.simps(3))
    also have "\<dots> = (\<not> isModel (setValuation S) (\<^bold>\<not> F))"
      by (simp only: isModel_def)
    finally show "\<not> isModel (setValuation S) (\<^bold>\<not> F)"
      by this
  qed
qed

lemma Hl2_2:
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

lemma Hl2_3:
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
    also have "(\<not> isModel (setValuation S) F1) = 
         (\<not> (setValuation S) \<Turnstile> F1)"
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


lemma Hl2_4:
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

lemma Hl2_5:
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
  show " (\<bottom> \<in> S \<longrightarrow> isModel (setValuation S) \<bottom>) \<and>
    (\<^bold>\<not> \<bottom> \<in> S \<longrightarrow> \<not> isModel (setValuation S) \<bottom>)" 
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
      have "\<bottom> \<notin> S"
        using assms by (rule Hintikka_l1)
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
next
  fix F
  show "(F \<in> S \<longrightarrow> isModel (setValuation S) F) \<and>
         (\<^bold>\<not> F \<in> S \<longrightarrow> \<not> isModel (setValuation S) F) \<Longrightarrow>
         (\<^bold>\<not> F \<in> S \<longrightarrow> isModel (setValuation S) (\<^bold>\<not> F)) \<and>
         (\<^bold>\<not> (\<^bold>\<not> F) \<in> S \<longrightarrow> \<not> isModel (setValuation S) (\<^bold>\<not> F))"
    using assms by (rule Hl2_2)
next
  fix F1 F2
  show "(F1 \<in> S \<longrightarrow> isModel (setValuation S) F1) \<and>
       (\<^bold>\<not> F1 \<in> S \<longrightarrow> \<not> isModel (setValuation S) F1) \<Longrightarrow>
       (F2 \<in> S \<longrightarrow> isModel (setValuation S) F2) \<and>
       (\<^bold>\<not> F2 \<in> S \<longrightarrow> \<not> isModel (setValuation S) F2) \<Longrightarrow>
       (F1 \<^bold>\<and> F2 \<in> S \<longrightarrow> isModel (setValuation S) (F1 \<^bold>\<and> F2)) \<and>
       (\<^bold>\<not> (F1 \<^bold>\<and> F2) \<in> S \<longrightarrow> \<not> isModel (setValuation S) (F1 \<^bold>\<and> F2))"
    using assms by (rule Hl2_3)
next
  fix F1 F2
  show "(F1 \<in> S \<longrightarrow> isModel (setValuation S) F1) \<and>
       (\<^bold>\<not> F1 \<in> S \<longrightarrow> \<not> isModel (setValuation S) F1) \<Longrightarrow>
       (F2 \<in> S \<longrightarrow> isModel (setValuation S) F2) \<and>
       (\<^bold>\<not> F2 \<in> S \<longrightarrow> \<not> isModel (setValuation S) F2) \<Longrightarrow>
       (F1 \<^bold>\<or> F2 \<in> S \<longrightarrow> isModel (setValuation S) (F1 \<^bold>\<or> F2)) \<and>
       (\<^bold>\<not> (F1 \<^bold>\<or> F2) \<in> S \<longrightarrow> \<not> isModel (setValuation S) (F1 \<^bold>\<or> F2))"
    using assms by (rule Hl2_4)
next
  fix F1 F2
  show "(F1 \<in> S \<longrightarrow> isModel (setValuation S) F1) \<and>
       (\<^bold>\<not> F1 \<in> S \<longrightarrow> \<not> isModel (setValuation S) F1) \<Longrightarrow>
       (F2 \<in> S \<longrightarrow> isModel (setValuation S) F2) \<and>
       (\<^bold>\<not> F2 \<in> S \<longrightarrow> \<not> isModel (setValuation S) F2) \<Longrightarrow>
       (F1 \<^bold>\<rightarrow> F2 \<in> S \<longrightarrow> isModel (setValuation S) (F1 \<^bold>\<rightarrow> F2)) \<and>
       (\<^bold>\<not> (F1 \<^bold>\<rightarrow> F2) \<in> S \<longrightarrow> \<not> isModel (setValuation S) (F1 \<^bold>\<rightarrow> F2))"
    using assms by (rule Hl2_5)
qed

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