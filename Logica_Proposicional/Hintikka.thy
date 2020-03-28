(*<*) 
theory Hintikka
  imports 
    Sintaxis
    Semantica
begin
(*>*)

section\<open>Lema de Hintikka\<close>

text \<open>We follow the proofs by Melvin Fitting~\cite{fitting1990first}.\<close>


text \<open>
Estas definiciones que están comentadas las había realizado yo en la semántica
de las fórmulas proposicionales. Tú tienes las mismas definiciones con otro
nombre. Tienes que adaptar esta teoría a los nombres que tienes ya definidos
y detallar todas las demostraciones. 

definition \<open>esModelo A F \<equiv> A \<Turnstile> F\<close>

definition \<open>esModeloConj A S \<equiv> \<forall>F. (F\<in> S \<longrightarrow> A \<Turnstile> F)\<close>

lemma modeloConjAlt:
  \<open>esModeloConj A S \<equiv> \<forall>F. (F\<in> S \<longrightarrow> esModelo A F)
  by (simp add: esModeloConj_def esModelo_def)\<close>

\<close>

text\<open>La teoría consiste en:
(+) Definir conjunto de Hintikka.
(+) Probar que todo conjunto de Hiktikka es consistente (satisfacible)
\<close>

text \<open> Definición: S es conjunto de Hintikka.\<close>

definition "Hintikka S \<equiv> 
( \<bottom> \<notin> S
  \<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
  \<and> (\<forall>F G. F \<^bold>\<and> G \<in> S \<longrightarrow> F \<in> S \<and> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<or> G \<in> S \<longrightarrow> F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> \<^bold>\<not>F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S)
)"

text\<open> Ejemplo:\<close>

notepad
begin

  have "Hintikka {Atom 0 \<^bold>\<and> ((\<^bold>\<not> (Atom 1)) \<^bold>\<rightarrow> Atom 2), 
                 ((\<^bold>\<not> (Atom 1)) \<^bold>\<rightarrow> Atom 2), 
                 Atom 0, \<^bold>\<not>(\<^bold>\<not> (Atom 1)), Atom 1}"
    unfolding Hintikka_def by simp

end

text \<open>Teorema: Todo conjunto de Hintikka es consistente.\<close>

definition interpretacionAsoc :: 
   "('a formula) set \<Rightarrow> 'a valuation" where
    "interpretacionAsoc S  \<equiv> \<lambda>k. Atom k \<in> S"

find_theorems name: atomize

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

lemma Hintikka_l1_detallada:
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

lemma Hintikka_l2_detallada:
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
  then have "\<forall>k. Atom k \<in> S \<longrightarrow> \<not> (\<^bold>\<not> (Atom k) \<in> S)"
    by (simp only: not_def)
  then have "\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<notin> S"
    by this
  then have "Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<notin> S"
    by (rule allE)
  thus "\<^bold>\<not> (Atom k) \<notin> S"
    using H by (rule mp)
qed

lemma Hintikka_l2: 
 "Hintikka S \<Longrightarrow>  (Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<notin> S)"
  by (smt Hintikka_def)

lemma Hintikka_l3_detallada: 
  assumes "Hintikka S"
  shows "F \<^bold>\<and> G \<in> S \<longrightarrow> F \<in> S \<and> G \<in> S"
proof (rule impI)
  assume H:"F \<^bold>\<and> G \<in> S"
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
  then have "(\<forall>F G. F \<^bold>\<and> G \<in> S \<longrightarrow> F \<in> S \<and> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<or> G \<in> S \<longrightarrow> F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> \<^bold>\<not>F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S)"
    by (rule conjunct2)
  then have "\<forall>F G. F \<^bold>\<and> G \<in> S \<longrightarrow> F \<in> S \<and> G \<in> S"
    by (rule conjunct1)
  then have "\<forall> G. F \<^bold>\<and> G \<in> S \<longrightarrow> F \<in> S \<and> G \<in> S"
    by (rule allE)
  then have "F \<^bold>\<and> G \<in> S \<longrightarrow> F \<in> S \<and> G \<in> S"
    by (rule allE)
  thus "F \<in> S \<and> G \<in> S"
    using H by (rule mp)
qed

lemma Hintikka_l3: 
 "Hintikka S \<Longrightarrow>  (F \<^bold>\<and> G \<in> S \<longrightarrow> F \<in> S \<and> G \<in> S)"
  by (smt Hintikka_def)

lemma Hintikka_l4_detallada: 
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
  then have "(\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
  \<and>(\<forall>F G. F \<^bold>\<and> G \<in> S \<longrightarrow> F \<in> S \<and> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<or> G \<in> S \<longrightarrow> F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> \<^bold>\<not>F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S)"
    by (rule conjunct2)
  then have "(\<forall>F G. F \<^bold>\<and> G \<in> S \<longrightarrow> F \<in> S \<and> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<or> G \<in> S \<longrightarrow> F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> \<^bold>\<not>F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S)"
    by (rule conjunct2)
  then have "(\<forall>F G. F \<^bold>\<or> G \<in> S \<longrightarrow> F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> \<^bold>\<not>F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S)"
    by (rule conjunct2)
  then have "\<forall>F G. F \<^bold>\<or> G \<in> S \<longrightarrow> F \<in> S \<or> G \<in> S"
    by (rule conjunct1)
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

lemma Hintikka_l5_detallada: 
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
  then have "(\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
  \<and>(\<forall>F G. F \<^bold>\<and> G \<in> S \<longrightarrow> F \<in> S \<and> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<or> G \<in> S \<longrightarrow> F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> \<^bold>\<not>F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S)"
    by (rule conjunct2)
  then have "(\<forall>F G. F \<^bold>\<and> G \<in> S \<longrightarrow> F \<in> S \<and> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<or> G \<in> S \<longrightarrow> F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> \<^bold>\<not>F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S)"
    by (rule conjunct2)
  then have "(\<forall>F G. F \<^bold>\<or> G \<in> S \<longrightarrow> F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> \<^bold>\<not>F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S)"
    by (rule conjunct2)
  then have "(\<forall>F G. F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> \<^bold>\<not>F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S)"
    by (rule conjunct2)
  then have "\<forall>F G. F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> \<^bold>\<not>F \<in> S \<or> G \<in> S"
    by (rule conjunct1)
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

lemma Hintikka_l6_detallada:
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
  then have "(\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
  \<and>(\<forall>F G. F \<^bold>\<and> G \<in> S \<longrightarrow> F \<in> S \<and> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<or> G \<in> S \<longrightarrow> F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> \<^bold>\<not>F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S)"
    by (rule conjunct2)
  then have "(\<forall>F G. F \<^bold>\<and> G \<in> S \<longrightarrow> F \<in> S \<and> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<or> G \<in> S \<longrightarrow> F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> \<^bold>\<not>F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S)"
    by (rule conjunct2)
  then have "(\<forall>F G. F \<^bold>\<or> G \<in> S \<longrightarrow> F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> \<^bold>\<not>F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S)"
    by (rule conjunct2)
  then have "(\<forall>F G. F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> \<^bold>\<not>F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S)"
    by (rule conjunct2)
  then have "(\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S)"
    by (rule conjunct2)
  then have "\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<in> S"
    by (rule conjunct1)
  then have "\<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<in> S"
    by (rule allE)
  thus "F \<in> S"
    using H by (rule mp)
qed

lemma Hintikka_l6: 
 "Hintikka S \<Longrightarrow>(\<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<in> S)"
  by (smt Hintikka_def)

lemma Hintikka_l7_detallada: 
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
  then have "(\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
  \<and>(\<forall>F G. F \<^bold>\<and> G \<in> S \<longrightarrow> F \<in> S \<and> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<or> G \<in> S \<longrightarrow> F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> \<^bold>\<not>F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S)"
    by (rule conjunct2)
  then have "(\<forall>F G. F \<^bold>\<and> G \<in> S \<longrightarrow> F \<in> S \<and> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<or> G \<in> S \<longrightarrow> F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> \<^bold>\<not>F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S)"
    by (rule conjunct2)
  then have "(\<forall>F G. F \<^bold>\<or> G \<in> S \<longrightarrow> F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> \<^bold>\<not>F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S)"
    by (rule conjunct2)
  then have "(\<forall>F G. F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> \<^bold>\<not>F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S)"
    by (rule conjunct2)
  then have "(\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S)"
    by (rule conjunct2)
  then have "(\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S)"
    by (rule conjunct2)
  then have "\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S"
    by (rule conjunct1)
  then have "\<forall>G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S"
    by (rule allE)
  then have "\<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S"
    by (rule allE)
    thus "\<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S"
      using H by (rule mp)
  qed

lemma Hintikka_l7: 
 "Hintikka S \<Longrightarrow> ( \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S)"
  by (smt Hintikka_def)

lemma Hintikka_l8_detallada: 
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
  then have "(\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
  \<and>(\<forall>F G. F \<^bold>\<and> G \<in> S \<longrightarrow> F \<in> S \<and> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<or> G \<in> S \<longrightarrow> F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> \<^bold>\<not>F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S)"
    by (rule conjunct2)
  then have "(\<forall>F G. F \<^bold>\<and> G \<in> S \<longrightarrow> F \<in> S \<and> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<or> G \<in> S \<longrightarrow> F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> \<^bold>\<not>F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S)"
    by (rule conjunct2)
  then have "(\<forall>F G. F \<^bold>\<or> G \<in> S \<longrightarrow> F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> \<^bold>\<not>F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S)"
    by (rule conjunct2)
  then have "(\<forall>F G. F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> \<^bold>\<not>F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S)"
    by (rule conjunct2)
  then have "(\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S)"
    by (rule conjunct2)
  then have "(\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S)"
    by (rule conjunct2)
  then have "(\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S)"
    by (rule conjunct2)
  then have "\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S"
    by (rule conjunct1)
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

lemma Hintikka_l9_detallada: 
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
  then have "(\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
  \<and>(\<forall>F G. F \<^bold>\<and> G \<in> S \<longrightarrow> F \<in> S \<and> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<or> G \<in> S \<longrightarrow> F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> \<^bold>\<not>F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S)"
    by (rule conjunct2)
  then have "(\<forall>F G. F \<^bold>\<and> G \<in> S \<longrightarrow> F \<in> S \<and> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<or> G \<in> S \<longrightarrow> F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> \<^bold>\<not>F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S)"
    by (rule conjunct2)
  then have "(\<forall>F G. F \<^bold>\<or> G \<in> S \<longrightarrow> F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F G. F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> \<^bold>\<not>F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S)"
    by (rule conjunct2)
  then have "(\<forall>F G. F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> \<^bold>\<not>F \<in> S \<or> G \<in> S)
  \<and> (\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S)"
    by (rule conjunct2)
  then have "(\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S)"
    by (rule conjunct2)
  then have "(\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S)"
    by (rule conjunct2)
  then have "(\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S)
  \<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S)"
    by (rule conjunct2)
  then have "\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S"
    by (rule conjunct2)
  then have "\<forall>G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S"
    by (rule allE)
  then have "\<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S"
    by (rule allE)
  thus "F \<in> S \<and> \<^bold>\<not> G \<in> S"
    using H by (rule mp)
qed

lemma Hintikka_l9: 
 "Hintikka S \<Longrightarrow> (\<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S)"
  by (smt Hintikka_def) 

lemma Hintikka_l10_detallada: 
  assumes "Hintikka S" 
  shows "\<^bold>\<not> F \<in> S \<longrightarrow> F \<notin> S"
  oops

lemma Hintikka_l10: 
 "Hintikka S \<Longrightarrow> (\<^bold>\<not> F \<in> S \<longrightarrow> F \<notin> S)"
  apply (induct F)
  apply (meson Hintikka_l2)
  apply (simp add: Hintikka_l1)
  using Hintikka_l6 apply blast
  using Hintikka_l3 Hintikka_l7 apply blast
  apply (smt Hintikka_def)
  using Hintikka_l5 Hintikka_l9 by blast


lemma Hl2_1_detallada:
  assumes  "Hintikka S"
  shows "\<And>x. (Atom x \<in> S \<longrightarrow> isModel (interpretacionAsoc S) (Atom x)) \<and>
         (\<^bold>\<not> (Atom x) \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) (Atom x))"
proof
  show " \<And>x. Atom x \<in> S \<longrightarrow> isModel (interpretacionAsoc S) (Atom x)" 
  proof
    fix x
    assume "Atom x \<in> S"
    hence "(interpretacionAsoc S) \<Turnstile> (Atom x)"
      by (simp add: interpretacionAsoc_def)
    thus "isModel (interpretacionAsoc S) (Atom x)"
      by (simp only: isModel_def)
  qed
next 
  show 
  "\<And>x. \<^bold>\<not> (Atom x) \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) (Atom x)" 
  proof
    fix x
    assume " \<^bold>\<not>  (Atom x) \<in> S" 
    hence "Atom x \<notin> S" using assms 
      by (simp add: \<open>\<^bold>\<not> (Atom x) \<in> S\<close> Hintikka_l10)
    thus "\<not> isModel (interpretacionAsoc S) (Atom x)"
      by (simp add: isModel_def interpretacionAsoc_def)
  qed
qed

lemma Hl2_1:
  assumes  "Hintikka S"
  shows "\<And>x. (Atom x \<in> S \<longrightarrow> isModel (interpretacionAsoc S) (Atom x)) \<and>
         (\<^bold>\<not> (Atom x) \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) (Atom x))"
  by (simp add: Hintikka_l10 assms isModel_def interpretacionAsoc_def)

lemma Hl2_3:
  assumes "Hintikka S"
  shows " \<And>F. (F \<in> S \<longrightarrow> isModel (interpretacionAsoc S) F) \<and>
         (\<^bold>\<not> F \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) F) \<Longrightarrow>
         (\<^bold>\<not> F \<in> S \<longrightarrow> isModel (interpretacionAsoc S) (\<^bold>\<not> F)) \<and>
         (\<^bold>\<not> (\<^bold>\<not> F) \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) (\<^bold>\<not> F))"
  using Hintikka_l6 assms isModel_def formula_semantics.simps(3) by blast

lemma Hl2_4:
  assumes "Hintikka S"
  shows "\<And>F1 F2.
       (F1 \<in> S \<longrightarrow> isModel (interpretacionAsoc S) F1) \<and>
       (\<^bold>\<not> F1 \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) F1) \<Longrightarrow>
       (F2 \<in> S \<longrightarrow> isModel (interpretacionAsoc S) F2) \<and>
       (\<^bold>\<not> F2 \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) F2) \<Longrightarrow>
       (F1 \<^bold>\<and> F2 \<in> S \<longrightarrow> isModel (interpretacionAsoc S) (F1 \<^bold>\<and> F2)) \<and>
       (\<^bold>\<not> (F1 \<^bold>\<and> F2) \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) (F1 \<^bold>\<and> F2))"
  by (meson Hintikka_l3 Hintikka_l7 assms isModel_def formula_semantics.simps(4))

lemma Hl2_5:
  assumes "Hintikka S"
  shows "\<And>F1 F2.
       (F1 \<in> S \<longrightarrow> isModel (interpretacionAsoc S) F1) \<and>
       (\<^bold>\<not> F1 \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) F1) \<Longrightarrow>
       (F2 \<in> S \<longrightarrow> isModel (interpretacionAsoc S) F2) \<and>
       (\<^bold>\<not> F2 \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) F2) \<Longrightarrow>
       (F1 \<^bold>\<or> F2 \<in> S \<longrightarrow> isModel (interpretacionAsoc S) (F1 \<^bold>\<or> F2)) \<and>
       (\<^bold>\<not> (F1 \<^bold>\<or> F2) \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) (F1 \<^bold>\<or> F2))"
  by (smt Hintikka_def assms isModel_def formula_semantics.simps(5))

lemma Hl2_6:
  assumes "Hintikka S"
  shows " \<And>F1 F2.
       (F1 \<in> S \<longrightarrow> isModel (interpretacionAsoc S) F1) \<and>
       (\<^bold>\<not> F1 \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) F1) \<Longrightarrow>
       (F2 \<in> S \<longrightarrow> isModel (interpretacionAsoc S) F2) \<and>
       (\<^bold>\<not> F2 \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) F2) \<Longrightarrow>
       (F1 \<^bold>\<rightarrow> F2 \<in> S \<longrightarrow> isModel (interpretacionAsoc S) (F1 \<^bold>\<rightarrow> F2)) \<and>
       (\<^bold>\<not> (F1 \<^bold>\<rightarrow> F2) \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) (F1 \<^bold>\<rightarrow> F2))"
  by (meson Hintikka_l5 Hintikka_l9 assms isModel_def formula_semantics.simps(6))

lemma Hintikkas_lemma_l2:
  assumes "Hintikka S"
  shows " (F \<in>S \<longrightarrow> isModel (interpretacionAsoc S) F)
           \<and> (\<^bold>\<not> F \<in> S \<longrightarrow> (\<not>(isModel (interpretacionAsoc S) F)))"
proof (induct F)
  fix x
  show "(Atom x \<in> S \<longrightarrow> isModel (interpretacionAsoc S) (Atom x)) \<and>
         (\<^bold>\<not> (Atom x) \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) (Atom x))"
    using assms by (rule Hl2_1)
next
  show " (\<bottom> \<in> S \<longrightarrow> isModel (interpretacionAsoc S) \<bottom>) \<and>
    (\<^bold>\<not> \<bottom> \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) \<bottom>)" 
    by (simp add: Hintikka_l1 assms isModel_def)
next
  fix F
  show "(F \<in> S \<longrightarrow> isModel (interpretacionAsoc S) F) \<and>
         (\<^bold>\<not> F \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) F) \<Longrightarrow>
         (\<^bold>\<not> F \<in> S \<longrightarrow> isModel (interpretacionAsoc S) (\<^bold>\<not> F)) \<and>
         (\<^bold>\<not> (\<^bold>\<not> F) \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) (\<^bold>\<not> F))"
    using assms by (rule Hl2_3)
next
  fix F1 F2
  show "(F1 \<in> S \<longrightarrow> isModel (interpretacionAsoc S) F1) \<and>
       (\<^bold>\<not> F1 \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) F1) \<Longrightarrow>
       (F2 \<in> S \<longrightarrow> isModel (interpretacionAsoc S) F2) \<and>
       (\<^bold>\<not> F2 \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) F2) \<Longrightarrow>
       (F1 \<^bold>\<and> F2 \<in> S \<longrightarrow> isModel (interpretacionAsoc S) (F1 \<^bold>\<and> F2)) \<and>
       (\<^bold>\<not> (F1 \<^bold>\<and> F2) \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) (F1 \<^bold>\<and> F2))"
    using assms by (rule Hl2_4)
next
  fix F1 F2
  show "(F1 \<in> S \<longrightarrow> isModel (interpretacionAsoc S) F1) \<and>
       (\<^bold>\<not> F1 \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) F1) \<Longrightarrow>
       (F2 \<in> S \<longrightarrow> isModel (interpretacionAsoc S) F2) \<and>
       (\<^bold>\<not> F2 \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) F2) \<Longrightarrow>
       (F1 \<^bold>\<or> F2 \<in> S \<longrightarrow> isModel (interpretacionAsoc S) (F1 \<^bold>\<or> F2)) \<and>
       (\<^bold>\<not> (F1 \<^bold>\<or> F2) \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) (F1 \<^bold>\<or> F2))"
    using assms by (rule Hl2_5)
next
  fix F1 F2
  show "(F1 \<in> S \<longrightarrow> isModel (interpretacionAsoc S) F1) \<and>
       (\<^bold>\<not> F1 \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) F1) \<Longrightarrow>
       (F2 \<in> S \<longrightarrow> isModel (interpretacionAsoc S) F2) \<and>
       (\<^bold>\<not> F2 \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) F2) \<Longrightarrow>
       (F1 \<^bold>\<rightarrow> F2 \<in> S \<longrightarrow> isModel (interpretacionAsoc S) (F1 \<^bold>\<rightarrow> F2)) \<and>
       (\<^bold>\<not> (F1 \<^bold>\<rightarrow> F2) \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) (F1 \<^bold>\<rightarrow> F2))"
    using assms by (rule Hl2_6)
qed

lemma Hintikka_modelo:
  assumes "Hintikka S"
  shows "isModelSet (interpretacionAsoc S) S"
proof-
  have " \<forall>F. (F\<in> S \<longrightarrow> isModel (interpretacionAsoc S) F)"
    by (simp add: Hintikkas_lemma_l2 assms)
  thus  "isModelSet (interpretacionAsoc S) S"
    by (simp only: modelSet)
qed 

(*theorem lemaDeHintikkas_det:
  assumes "Hintikka S"
  shows "sat S"
proof-
  have "isModelSet (interpretacionAsoc S) S"
    using assms by (rule Hintikka_modelo)
  thus "sat S" using satAlt by blast
qed

theorem lemaDeHintikkas:
  assumes "Hintikka S"
  shows "sat S"
  using Hintikka_modelo assms satAlt by blast*)


(*<*)
end
(*>*) 