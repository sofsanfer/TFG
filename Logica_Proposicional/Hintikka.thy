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
 "Hintikka S \<Longrightarrow> \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<in> S"
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
 "Hintikka S \<Longrightarrow> \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S"
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
 "Hintikka S \<Longrightarrow> \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S"
  by (smt Hintikka_def) 

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

text \<open>\comentario{Desarrollar notnotI.}

  \comentario{Aplicar mt en las demostraciones posteriores.}\<close>

lemma notnotI: "P \<Longrightarrow> \<not>\<not> P"
  by auto

lemma Hintikka_l10_atom: 
  assumes "Hintikka S" 
  shows "\<^bold>\<not> (Atom x) \<in> S \<longrightarrow> Atom x \<notin> S"
proof (rule impI)
  assume "\<^bold>\<not> (Atom x) \<in> S"
  then have "\<not>(\<^bold>\<not> (Atom x) \<notin> S)"
    by (rule notnotI)
  have "Atom x \<in> S \<longrightarrow> \<^bold>\<not> (Atom x) \<notin> S"
    using assms by (rule Hintikka_l2)
  then have "\<not>(\<^bold>\<not> (Atom x) \<notin> S) \<longrightarrow> Atom x \<notin> S"
    by (rule not_mono)
  thus "Atom x \<notin> S"
    using \<open>\<not> (\<^bold>\<not> (Atom x) \<notin> S) \<close>by (rule mp)
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
  assumes "Hintikka S" 
          "\<^bold>\<not> F \<in> S \<longrightarrow> F \<notin> S"
        shows "\<^bold>\<not> (\<^bold>\<not> F) \<in> S \<longrightarrow> \<^bold>\<not> F \<notin> S"
proof (rule impI)
  assume "\<^bold>\<not> (\<^bold>\<not> F) \<in> S"
  have "\<^bold>\<not> (\<^bold>\<not> F) \<in> S \<longrightarrow> F \<in> S"
    using assms(1) by (rule Hintikka_l6)
  then have "F \<in> S"
    using \<open>\<^bold>\<not> (\<^bold>\<not> F) \<in> S\<close> by (rule mp)
  then have "\<not> (F \<notin> S)"
    by (rule notnotI)
  have "\<not> (F \<notin> S) \<longrightarrow> \<^bold>\<not> F \<notin> S"
    using assms(2) by (rule not_mono)
  thus "\<^bold>\<not> F \<notin> S"
    using \<open>\<not> (F \<notin> S)\<close> by (rule mp)
qed

text \<open>\comentario{No entiendo por qué en estos casos que he dejado 
  como pendiente no permite usar rule notnotD}\<close>

find_theorems -name: conj disj
find_theorems "\<lbrakk>\<not>_; \<not>_\<rbrakk> \<Longrightarrow> \<not>(_ \<and> _)"
find_theorems "\<not> _ \<and> \<not> _ = (\<not> (_ \<and> _))"

lemma Hintikka_l10_and: 
  assumes "Hintikka S" 
          "\<^bold>\<not> G \<in> S \<longrightarrow> G \<notin> S"
          "\<^bold>\<not> H \<in> S \<longrightarrow> H \<notin> S"
  shows "\<^bold>\<not> (G \<^bold>\<and> H) \<in> S \<longrightarrow> (G \<^bold>\<and> H) \<notin> S"
proof (rule impI)
  assume "\<^bold>\<not> (G \<^bold>\<and> H) \<in> S"
  have "\<^bold>\<not> (G \<^bold>\<and> H) \<in> S \<longrightarrow> \<^bold>\<not> G \<in> S \<or> \<^bold>\<not> H \<in> S"
    using assms(1) by (rule Hintikka_l7)
  then have "\<^bold>\<not> G \<in> S \<or> \<^bold>\<not> H \<in> S"
    using \<open>\<^bold>\<not> (G \<^bold>\<and> H) \<in> S\<close> by (rule mp)
  then show "G \<^bold>\<and> H \<notin> S"
  proof (rule disjE)
    assume "\<^bold>\<not> G \<in> S"
    have "\<not> (G \<in> S)"
      using assms(2) \<open>\<^bold>\<not> G \<in> S\<close> by (rule mp)
    have "\<not> (G \<in> S \<and> H \<in> S)"
    proof (rule ccontr)
      assume "\<not> \<not> (G \<in> S \<and> H \<in> S)"
      then have "G \<in> S \<and> H \<in> S"
        by (rule notnotD)
      then have "G \<in> S"
        by (rule conjunct1)
      show "False"
        using \<open>G \<notin> S\<close> \<open>G \<in> S\<close> by (rule notE)
    qed
    have "(G \<^bold>\<and> H \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S)"
      using assms(1) by (rule Hintikka_l3)
    thus "G \<^bold>\<and> H \<notin> S"
      using \<open>\<not> (G \<in> S \<and> H \<in> S)\<close>  by (rule mt)
  next
    assume "\<^bold>\<not> H \<in> S"
    have "H \<notin> S"
      using assms(3) \<open>\<^bold>\<not> H \<in> S\<close> by (rule mp)
    have "\<not> (G \<in> S \<and> H \<in> S)" 
    proof (rule ccontr)
      assume "\<not> \<not> (G \<in> S \<and> H \<in> S)"
      then have "G \<in> S \<and> H \<in> S"
        by (rule notnotD)
      then have "H \<in> S"
        by (rule conjunct2)
      show "False"
        using \<open>H \<notin> S\<close> \<open>H \<in> S\<close> by (rule notE)
    qed
    have "(G \<^bold>\<and> H \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S)"
      using assms(1) by (rule Hintikka_l3)
    thus "G \<^bold>\<and> H \<notin> S"
      using \<open>\<not> (G \<in> S \<and> H \<in> S)\<close> by (rule mt)
  qed
qed

lemma Hintikka_l10_or: 
  assumes "Hintikka S" 
          "\<^bold>\<not> G \<in> S \<longrightarrow> G \<notin> S"
          "\<^bold>\<not> H \<in> S \<longrightarrow> H \<notin> S"
  shows "\<^bold>\<not> (G \<^bold>\<or> H) \<in> S \<longrightarrow> (G \<^bold>\<or> H) \<notin> S"
proof (rule impI)
  assume "\<^bold>\<not> (G \<^bold>\<or> H) \<in> S"
  have "\<^bold>\<not> (G \<^bold>\<or> H) \<in> S \<longrightarrow> (\<^bold>\<not> G \<in> S \<and> \<^bold>\<not> H \<in> S)"
    using assms(1) by (rule Hintikka_l8)
  then have C:"\<^bold>\<not> G \<in> S \<and> \<^bold>\<not> H \<in> S"
    using \<open>\<^bold>\<not> (G \<^bold>\<or> H) \<in> S\<close> by (rule mp)
  then have "\<^bold>\<not> G \<in> S"
    by (rule conjunct1)
  have "G \<notin> S" 
    using assms(2) \<open>\<^bold>\<not> G \<in> S\<close> by (rule mp) 
  have "\<^bold>\<not> H \<in> S"
    using C by (rule conjunct2)
  have "H \<notin> S" 
    using assms(3) \<open>\<^bold>\<not> H \<in> S\<close> by (rule mp)
  have "\<not> (G \<in> S \<or> H \<in> S)"
    using \<open>G \<notin> S\<close> \<open>H \<notin> S\<close> by simp (*Pendiente*)
  have "(G \<^bold>\<or> H \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S)"
    using assms(1) by (rule Hintikka_l4)
  then have "\<not> (G \<in> S \<or> H \<in> S) \<longrightarrow> \<not> (G \<^bold>\<or> H \<in> S)"
    by (rule not_mono)
  thus "G \<^bold>\<or> H \<notin> S"
    using \<open>\<not> (G \<in> S \<or> H \<in> S)\<close> by (rule mp)
qed

find_theorems name: notnot

lemma Hintikka_l10_imp: 
  assumes "Hintikka S" 
          "\<^bold>\<not> G \<in> S \<longrightarrow> G \<notin> S"
          "\<^bold>\<not> H \<in> S \<longrightarrow> H \<notin> S"
  shows "\<^bold>\<not> (G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> (G \<^bold>\<rightarrow> H) \<notin> S"
proof (rule impI)
  assume "\<^bold>\<not> (G \<^bold>\<rightarrow> H) \<in> S"
  have "\<^bold>\<not> (G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> (G \<in> S \<and> \<^bold>\<not> H \<in> S)"
    using assms(1) by (rule Hintikka_l9)
  then have C:"G \<in> S \<and> \<^bold>\<not> H \<in> S"
    using \<open>\<^bold>\<not> (G \<^bold>\<rightarrow> H) \<in> S\<close> by (rule mp)
  then have "G \<in> S"
    by (rule conjunct1)
  then have "\<not> \<not> G \<in> S"
    by (rule notnotI)
  have "\<not> \<not> (G \<in> S) \<longrightarrow> \<^bold>\<not> G \<notin> S"
    using assms(2) by (rule not_mono)
  then have "\<^bold>\<not> G \<notin> S"
    using \<open>\<not>\<not> G \<in> S\<close> by (rule mp)
  have "\<^bold>\<not> H \<in> S"
    using C by (rule conjunct2)
  have "H \<notin> S"
    using assms(3) \<open>\<^bold>\<not> H \<in> S\<close> by (rule mp)
  have "\<not> (\<^bold>\<not> G \<in> S \<or> H \<in> S)"
    using \<open>\<^bold>\<not> G \<notin> S\<close> \<open>H \<notin> S\<close> by simp (*Pendiente*)
  have "(G \<^bold>\<rightarrow> H \<in> S \<longrightarrow> \<^bold>\<not>G \<in> S \<or> H \<in> S)"
    using assms(1) by (rule Hintikka_l5)
  thus "G \<^bold>\<rightarrow> H \<notin> S"
    using \<open>\<not> (\<^bold>\<not> G \<in> S \<or> H \<in> S)\<close> by (rule mt)
qed

(*lemma Hintikka_l10_detallada: 
  assumes "Hintikka S" 
  shows "\<^bold>\<not> F \<in> S \<longrightarrow> F \<notin> S"
proof (induct F)
case (Atom x)
  then show ?case
    using assms by (rule Hintikka_l10_atom)
next
  case Bot
  then show ?case
    using assms by (rule Hintikka_l10_bot)
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
qed*)

text \<open>\comentario{No entiendo el error en Hintikka l10 detallada.}\<close>

lemma Hintikka_l10: 
 "Hintikka S \<Longrightarrow> (\<^bold>\<not> F \<in> S \<longrightarrow> F \<notin> S)"
  apply (induct F)
  apply (meson Hintikka_l2)
  apply (simp add: Hintikka_l1)
  using Hintikka_l6 apply blast
  using Hintikka_l3 Hintikka_l7 apply blast
  apply (smt Hintikka_def)
  using Hintikka_l5 Hintikka_l9 by blast

text \<open>\comentario{Hasta aquí solo tengo las dudas anteriores. Sigo
  trabajando en sucio en las siguientes líneas.}\<close>

lemma Hl2_1_detallada:
  assumes  "Hintikka S"
  shows "\<And>x. (Atom x \<in> S \<longrightarrow> isModel (interpretacionAsoc S) (Atom x)) \<and>
         (\<^bold>\<not> (Atom x) \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) (Atom x))"
proof (rule conjI)
  show "\<And>x. Atom x \<in> S \<longrightarrow> isModel (interpretacionAsoc S) (Atom x)" 
  proof (rule impI)
    fix x
    assume "Atom x \<in> S"
    hence "(interpretacionAsoc S) x"
      by (simp only: interpretacionAsoc_def)
    hence "(interpretacionAsoc S) \<Turnstile> (Atom x)"
      by (simp only: formula_semantics.simps(1))
    thus "isModel (interpretacionAsoc S) (Atom x)"
      by (simp only: isModel_def)
  qed
next 
  show 
  "\<And>x. \<^bold>\<not> (Atom x) \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) (Atom x)" 
  proof (rule impI)
    fix x
    assume I:" \<^bold>\<not> (Atom x) \<in> S" 
    have "\<^bold>\<not> (Atom x) \<in> S \<longrightarrow> Atom x \<notin> S"
      using assms by (rule Hintikka_l10)
    then have "\<not> (Atom x \<in> S)"
      using I by (rule mp)
    hence "\<not> ((interpretacionAsoc S) x)"
      by (simp add: interpretacionAsoc_def) (*Pendiente*)
    hence "\<not> ((interpretacionAsoc S) \<Turnstile> (Atom x))"
      by simp (*(simp only: formula_semantics.simps(1)) Pendiente*)
    thus "\<not> isModel (interpretacionAsoc S) (Atom x)" 
      by (simp add: isModel_def) (*Pendiente*)
  qed
qed

lemma Hl2_1:
  assumes  "Hintikka S"
  shows "\<And>x. (Atom x \<in> S \<longrightarrow> isModel (interpretacionAsoc S) (Atom x)) \<and>
         (\<^bold>\<not> (Atom x) \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) (Atom x))"
  by (simp add: Hintikka_l10 assms isModel_def interpretacionAsoc_def) 

lemma Hl2_2_detallada:
  assumes "Hintikka S"
          "\<And>F. (F \<in> S \<longrightarrow> isModel (interpretacionAsoc S) F) \<and>
         (\<^bold>\<not> F \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) F)"
  shows "\<And>F. (\<^bold>\<not> F \<in> S \<longrightarrow> isModel (interpretacionAsoc S) (\<^bold>\<not> F)) \<and>
         (\<^bold>\<not> (\<^bold>\<not> F) \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) (\<^bold>\<not> F))"
proof (rule conjI) 
  show "\<And>F. \<^bold>\<not> F \<in> S \<longrightarrow> isModel (interpretacionAsoc S) (\<^bold>\<not> F)"
  proof (rule impI)
    fix F
    assume "\<^bold>\<not> F \<in> S"
    have "\<^bold>\<not> F \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) F"
      using assms(2) by (rule conjunct2)
    then have "\<not> isModel (interpretacionAsoc S) F"
      using  \<open>\<^bold>\<not> F \<in> S\<close> by (rule mp)
    then have "\<not> (interpretacionAsoc S) \<Turnstile> F"
      by (simp add: isModel_def) (*Pendiente*)
    then have "(interpretacionAsoc S) \<Turnstile> (\<^bold>\<not> F)"
      by simp (*(simp only: formula_semantics.simps(3)) Pendiente*)
    thus "isModel (interpretacionAsoc S) (\<^bold>\<not> F)"
      by (simp only: isModel_def)
  qed
next
  show "\<And>F. \<^bold>\<not> (\<^bold>\<not> F) \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) (\<^bold>\<not> F)"
  proof (rule impI)
    fix F
    assume "\<^bold>\<not> (\<^bold>\<not> F) \<in> S"
    have "\<^bold>\<not> (\<^bold>\<not> F) \<in> S \<longrightarrow> F \<in> S" 
      using assms(1) by (rule Hintikka_l6)
    then have "F \<in> S"
      using \<open>\<^bold>\<not> (\<^bold>\<not> F) \<in> S\<close> by (rule mp)
    have "F \<in> S \<longrightarrow> isModel (interpretacionAsoc S) F" 
      using assms(2) by (rule conjunct1)
    then have "isModel (interpretacionAsoc S) F"
      using \<open>F \<in> S\<close> by (rule mp)
    then have "\<not> (\<not> isModel (interpretacionAsoc S) F)"
      by (rule notnotI)
    then have "\<not> (\<not> (interpretacionAsoc S) \<Turnstile> F)"
      by (simp add: isModel_def) (*Pendiente*)
    then have "\<not> (interpretacionAsoc S) \<Turnstile> (\<^bold>\<not> F)"
      by simp (*Pendiente*)
    thus "\<not> isModel (interpretacionAsoc S) (\<^bold>\<not> F)"
      by (simp add: isModel_def) (*Pendiente*)
  qed
qed

lemma Hl2_2:
  assumes "Hintikka S"
  shows " \<And>F. (F \<in> S \<longrightarrow> isModel (interpretacionAsoc S) F) \<and>
         (\<^bold>\<not> F \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) F) \<Longrightarrow>
         (\<^bold>\<not> F \<in> S \<longrightarrow> isModel (interpretacionAsoc S) (\<^bold>\<not> F)) \<and>
         (\<^bold>\<not> (\<^bold>\<not> F) \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) (\<^bold>\<not> F))"
  using Hintikka_l6 assms isModel_def formula_semantics.simps(3) by blast

lemma Hl2_3_detallada:
  assumes "Hintikka S"
          "\<And>F1. (F1 \<in> S \<longrightarrow> isModel (interpretacionAsoc S) F1) \<and>
           (\<^bold>\<not> F1 \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) F1)" 
          "\<And>F2. (F2 \<in> S \<longrightarrow> isModel (interpretacionAsoc S) F2) \<and>
           (\<^bold>\<not> F2 \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) F2)"
  shows "\<And>F1 F2. (F1 \<^bold>\<and> F2 \<in> S \<longrightarrow> isModel (interpretacionAsoc S) (F1 \<^bold>\<and> F2)) \<and>
       (\<^bold>\<not> (F1 \<^bold>\<and> F2) \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) (F1 \<^bold>\<and> F2))"
proof (rule conjI)
  show "\<And>F1 F2. F1 \<^bold>\<and> F2 \<in> S \<longrightarrow> isModel (interpretacionAsoc S) (F1 \<^bold>\<and> F2)"
  proof (rule impI)
    fix F1 F2
    assume "F1 \<^bold>\<and> F2 \<in> S"
    have "F1 \<^bold>\<and> F2 \<in> S \<longrightarrow> F1 \<in> S \<and> F2 \<in> S"
      using assms(1) by (rule Hintikka_l3)
    then have C:"F1 \<in> S \<and> F2 \<in> S"
      using \<open>F1 \<^bold>\<and> F2 \<in> S\<close> by (rule mp)
    then have "F1 \<in> S" 
      by (rule conjunct1)
    have "F1 \<in> S \<longrightarrow> isModel (interpretacionAsoc S) F1"
      using assms(2) by (rule conjunct1)
    then have "isModel (interpretacionAsoc S) F1"
      using \<open>F1 \<in> S\<close> by (rule mp)
    then have I1:"(interpretacionAsoc S) \<Turnstile> F1"
      by (simp only: isModel_def)
    have "F2 \<in> S"
      using C by (rule conjunct2)
    have "F2 \<in> S \<longrightarrow> isModel (interpretacionAsoc S) F2"
      using assms(3) by (rule conjunct1)
    then have "isModel (interpretacionAsoc S) F2"
      using \<open>F2 \<in> S\<close> by (rule mp)
    then have I2:"(interpretacionAsoc S) \<Turnstile> F2"
      by (simp only: isModel_def) 
    have "((interpretacionAsoc S) \<Turnstile> F1) \<and> ((interpretacionAsoc S) \<Turnstile> F2)"
      using I1 I2 by (rule conjI)
    then have "(interpretacionAsoc S) \<Turnstile> (F1 \<^bold>\<and> F2)"
      by (simp only: formula_semantics.simps(4))
    thus "isModel (interpretacionAsoc S) (F1 \<^bold>\<and> F2)"
      by (simp only: isModel_def) 
  qed
next
  show "\<And>F1 F2. \<^bold>\<not> (F1 \<^bold>\<and> F2) \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) (F1 \<^bold>\<and> F2)"
  proof (rule impI)
    fix F1 F2
    assume "\<^bold>\<not> (F1 \<^bold>\<and> F2) \<in> S"
    have "\<^bold>\<not> (F1 \<^bold>\<and> F2) \<in> S \<longrightarrow> \<^bold>\<not> F1 \<in> S \<or> \<^bold>\<not> F2 \<in> S"
      using assms(1) by (rule Hintikka_l7)
    then have "\<^bold>\<not> F1 \<in> S \<or> \<^bold>\<not> F2 \<in> S"
      using \<open>\<^bold>\<not> (F1 \<^bold>\<and> F2) \<in> S\<close> by (rule mp)
    then show "\<not> isModel (interpretacionAsoc S) (F1 \<^bold>\<and> F2)"
    proof (rule disjE)
      assume "\<^bold>\<not> F1 \<in> S"
      have "\<^bold>\<not> F1 \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) F1"
        using assms(2) by (rule conjunct2)
      then have "\<not> isModel (interpretacionAsoc S) F1"
        using \<open>\<^bold>\<not> F1 \<in> S\<close> by (rule mp)
      then have "\<not> ((interpretacionAsoc S) \<Turnstile> F1)"
        by (simp add: isModel_def) (*Pendiente*)
      then have "\<not> ((interpretacionAsoc S) \<Turnstile> F1 \<and> (interpretacionAsoc S) \<Turnstile> F2)" 
        by simp (*Pendiente*)
      then have "\<not> ((interpretacionAsoc S) \<Turnstile> (F1 \<^bold>\<and> F2))"
        by simp (*Pendiente: (simp only: formula_semantics.simps(4))*)
      thus "\<not> isModel (interpretacionAsoc S) (F1 \<^bold>\<and> F2)"
        by (simp add: isModel_def) (*Pendiente*)
    next
      assume "\<^bold>\<not> F2 \<in> S"
      have "\<^bold>\<not> F2 \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) F2"
        using assms(3) by (rule conjunct2)
      then have "\<not> isModel (interpretacionAsoc S) F2"
        using \<open>\<^bold>\<not> F2 \<in> S\<close> by (rule mp)
      then have "\<not> ((interpretacionAsoc S) \<Turnstile> F2)"
        by (simp add: isModel_def) (*Pendiente*)
      then have "\<not> ((interpretacionAsoc S) \<Turnstile> F1 \<and> (interpretacionAsoc S) \<Turnstile> F2)" 
        by simp (*Pendiente*)
      then have "\<not> ((interpretacionAsoc S) \<Turnstile> (F1 \<^bold>\<and> F2))"
        by simp (*Pendiente: (simp only: formula_semantics.simps(4))*)
      thus "\<not> isModel (interpretacionAsoc S) (F1 \<^bold>\<and> F2)"
        by (simp add: isModel_def) (*Pendiente*)
    qed
  qed
qed


lemma Hl2_3:
  assumes "Hintikka S"
  shows "\<And>F1 F2.
       (F1 \<in> S \<longrightarrow> isModel (interpretacionAsoc S) F1) \<and>
       (\<^bold>\<not> F1 \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) F1) \<Longrightarrow>
       (F2 \<in> S \<longrightarrow> isModel (interpretacionAsoc S) F2) \<and>
       (\<^bold>\<not> F2 \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) F2) \<Longrightarrow>
       (F1 \<^bold>\<and> F2 \<in> S \<longrightarrow> isModel (interpretacionAsoc S) (F1 \<^bold>\<and> F2)) \<and>
       (\<^bold>\<not> (F1 \<^bold>\<and> F2) \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) (F1 \<^bold>\<and> F2))"
  by (meson Hintikka_l3 Hintikka_l7 assms isModel_def formula_semantics.simps(4))

lemma Hl2_4_detallada:
  assumes "Hintikka S"
          "\<And>F1. (F1 \<in> S \<longrightarrow> isModel (interpretacionAsoc S) F1) \<and>
           (\<^bold>\<not> F1 \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) F1)" 
          "\<And>F2. (F2 \<in> S \<longrightarrow> isModel (interpretacionAsoc S) F2) \<and>
           (\<^bold>\<not> F2 \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) F2)"
  shows "\<And>F1 F2. (F1 \<^bold>\<or> F2 \<in> S \<longrightarrow> isModel (interpretacionAsoc S) (F1 \<^bold>\<or> F2)) 
  \<and> (\<^bold>\<not> (F1 \<^bold>\<or> F2) \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) (F1 \<^bold>\<or> F2))"
proof (rule conjI)
  show "\<And> F1 F2. F1 \<^bold>\<or> F2 \<in> S \<longrightarrow> isModel (interpretacionAsoc S) (F1 \<^bold>\<or> F2)"
  proof (rule impI)
    fix F1 F2
    assume "F1 \<^bold>\<or> F2 \<in> S"
    have "F1 \<^bold>\<or> F2 \<in> S \<longrightarrow> F1 \<in> S \<or> F2 \<in> S"
      using assms(1) by (rule Hintikka_l4)
    then have "F1 \<in> S \<or> F2 \<in> S"
      using \<open>F1 \<^bold>\<or> F2 \<in> S\<close> by (rule mp)
    then show "isModel (interpretacionAsoc S) (F1 \<^bold>\<or> F2)"
    proof (rule disjE)
      assume "F1 \<in> S"
      have "F1 \<in> S \<longrightarrow> isModel (interpretacionAsoc S) F1"
        using assms(2) by (rule conjunct1)
      then have "isModel (interpretacionAsoc S) F1" 
        using \<open>F1 \<in> S\<close> by (rule mp)
      then have "(interpretacionAsoc S) \<Turnstile> F1"
        by (simp only: isModel_def)
      then have "(interpretacionAsoc S) \<Turnstile> F1 \<or> (interpretacionAsoc S) \<Turnstile> F2"
        by (rule disjI1)
      then have "(interpretacionAsoc S) \<Turnstile> (F1 \<^bold>\<or> F2)"
        by (simp only: formula_semantics.simps(5))
      thus "isModel (interpretacionAsoc S) (F1 \<^bold>\<or> F2)"
        by (simp only: isModel_def)
    next
      assume "F2 \<in> S"
      have "F2 \<in> S \<longrightarrow> isModel (interpretacionAsoc S) F2"
        using assms(3) by (rule conjunct1)
      then have "isModel (interpretacionAsoc S) F2" 
        using \<open>F2 \<in> S\<close> by (rule mp)
      then have "(interpretacionAsoc S) \<Turnstile> F2"
        by (simp only: isModel_def)
      then have "(interpretacionAsoc S) \<Turnstile> F1 \<or> (interpretacionAsoc S) \<Turnstile> F2"
        by (rule disjI2)
      then have "(interpretacionAsoc S) \<Turnstile> (F1 \<^bold>\<or> F2)"
        by (simp only: formula_semantics.simps(5))
      thus "isModel (interpretacionAsoc S) (F1 \<^bold>\<or> F2)"
        by (simp only: isModel_def)
    qed
  qed
next
  show "\<And>F1 F2. \<^bold>\<not> (F1 \<^bold>\<or> F2) \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) (F1 \<^bold>\<or> F2)"
  proof (rule impI)
    fix F1 F2
    assume "\<^bold>\<not> (F1 \<^bold>\<or> F2) \<in> S"
    have "\<^bold>\<not> (F1 \<^bold>\<or> F2) \<in> S \<longrightarrow> \<^bold>\<not> F1 \<in> S \<and> \<^bold>\<not> F2 \<in> S"
      using assms(1) by (rule Hintikka_l8)
    then have C:"\<^bold>\<not> F1 \<in> S \<and> \<^bold>\<not> F2 \<in> S"
      using \<open>\<^bold>\<not> (F1 \<^bold>\<or> F2) \<in> S\<close> by (rule mp)
    then have "\<^bold>\<not> F1 \<in> S"
      by (rule conjunct1)
    have "\<^bold>\<not> F1 \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) F1"
      using assms(2) by (rule conjunct2)
    then have "\<not> isModel (interpretacionAsoc S) F1"
      using \<open>\<^bold>\<not> F1 \<in> S\<close> by (rule mp)
    then have D1:"\<not> (interpretacionAsoc S) \<Turnstile> F1"
      by (simp add: isModel_def) (*Pendiente*)
    have "\<^bold>\<not> F2 \<in> S"
      using C by (rule conjunct2)
    have "\<^bold>\<not> F2 \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) F2"
      using assms(3) by (rule conjunct2)
    then have "\<not> isModel (interpretacionAsoc S) F2"
      using \<open>\<^bold>\<not> F2 \<in> S\<close> by (rule mp)
    then have D2:"\<not> (interpretacionAsoc S) \<Turnstile> F2"
      by (simp add: isModel_def) (*Pendiente*)
    have "\<not> ((interpretacionAsoc S) \<Turnstile> F1 \<or> (interpretacionAsoc S) \<Turnstile> F2)"
      using D1 D2 by simp (*Pendiente*)
    then have "\<not> (interpretacionAsoc S) \<Turnstile> (F1 \<^bold>\<or> F2)"
      by simp (*Pendiente (simp only: formula_semantics.simps(5))*)
    thus "\<not> isModel (interpretacionAsoc S) (F1 \<^bold>\<or> F2)"
      by (simp add: isModel_def) (*Pendiente*)
  qed
qed


lemma Hl2_4:
  assumes "Hintikka S"
  shows "\<And>F1 F2.
       (F1 \<in> S \<longrightarrow> isModel (interpretacionAsoc S) F1) \<and>
       (\<^bold>\<not> F1 \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) F1) \<Longrightarrow>
       (F2 \<in> S \<longrightarrow> isModel (interpretacionAsoc S) F2) \<and>
       (\<^bold>\<not> F2 \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) F2) \<Longrightarrow>
       (F1 \<^bold>\<or> F2 \<in> S \<longrightarrow> isModel (interpretacionAsoc S) (F1 \<^bold>\<or> F2)) \<and>
       (\<^bold>\<not> (F1 \<^bold>\<or> F2) \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) (F1 \<^bold>\<or> F2))"
  by (smt Hintikka_def assms isModel_def formula_semantics.simps(5))

lemma Hl2_5_detallada:
  assumes "Hintikka S"
          "\<And>F1. (F1 \<in> S \<longrightarrow> isModel (interpretacionAsoc S) F1) \<and>
           (\<^bold>\<not> F1 \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) F1)" 
          "\<And>F2. (F2 \<in> S \<longrightarrow> isModel (interpretacionAsoc S) F2) \<and>
           (\<^bold>\<not> F2 \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) F2)"
  shows "\<And>F1 F2. (F1 \<^bold>\<rightarrow> F2 \<in> S \<longrightarrow> isModel (interpretacionAsoc S) (F1 \<^bold>\<rightarrow> F2)) 
      \<and> (\<^bold>\<not> (F1 \<^bold>\<rightarrow> F2) \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) (F1 \<^bold>\<rightarrow> F2))"
proof (rule conjI)
  show "\<And>F1 F2. F1 \<^bold>\<rightarrow> F2 \<in> S \<longrightarrow> isModel (interpretacionAsoc S) (F1 \<^bold>\<rightarrow> F2)"
  proof (rule impI)
    fix F1 F2
    assume "F1 \<^bold>\<rightarrow> F2 \<in> S"
    have "F1 \<^bold>\<rightarrow> F2 \<in> S \<longrightarrow> \<^bold>\<not> F1 \<in> S \<or> F2 \<in> S"
      using assms(1) by (rule Hintikka_l5)
    then have "\<^bold>\<not> F1 \<in> S \<or> F2 \<in> S"
      using \<open>F1 \<^bold>\<rightarrow> F2 \<in> S\<close> by (rule mp)
    then show "isModel (interpretacionAsoc S) (F1 \<^bold>\<rightarrow> F2)"
    proof (rule disjE)
      assume "\<^bold>\<not> F1 \<in> S"
      have "\<^bold>\<not> F1 \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) F1"
        using assms(2) by (rule conjunct2)
      then have "\<not> isModel (interpretacionAsoc S) F1"
        using \<open>\<^bold>\<not> F1 \<in> S\<close> by (rule mp)
      then have N1:"\<not> (interpretacionAsoc S) \<Turnstile> F1"
        by (simp add: isModel_def) (*Pendiente*)
      have "(interpretacionAsoc S) \<Turnstile> F1 \<longrightarrow> (interpretacionAsoc S) \<Turnstile> F2"
      proof (rule impI)
        assume N2:"(interpretacionAsoc S) \<Turnstile> F1"
        show "(interpretacionAsoc S) \<Turnstile> F2"
          using N1 N2 by (rule notE) 
      qed
      then have "(interpretacionAsoc S) \<Turnstile> (F1 \<^bold>\<rightarrow> F2)"
        by (simp only: formula_semantics.simps(6))
      thus ?thesis
        by (simp only: isModel_def)
    next
      assume "F2 \<in> S"
      have "F2 \<in> S \<longrightarrow> isModel (interpretacionAsoc S) F2"
        using assms(3) by (rule conjunct1)
      then have "isModel (interpretacionAsoc S) F2"
        using \<open>F2 \<in> S\<close> by (rule mp)
      then have N:"(interpretacionAsoc S) \<Turnstile> F2"
        by (simp only: isModel_def)
      have "(interpretacionAsoc S) \<Turnstile> F1 \<longrightarrow> (interpretacionAsoc S) \<Turnstile> F2"
      proof (rule impI)
        assume "(interpretacionAsoc S) \<Turnstile> F1"
        show "(interpretacionAsoc S) \<Turnstile> F2"
          using N by this 
      qed
      then have "(interpretacionAsoc S) \<Turnstile> (F1 \<^bold>\<rightarrow> F2)"
        by (simp only: formula_semantics.simps(6))
      thus ?thesis
        by (simp only: isModel_def)
    qed
  qed
next
  show "\<And>F1 F2. \<^bold>\<not> (F1 \<^bold>\<rightarrow> F2) \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) (F1 \<^bold>\<rightarrow> F2)"
  proof (rule impI)
    fix F1 F2
    assume "\<^bold>\<not> (F1 \<^bold>\<rightarrow> F2) \<in> S"
    have "\<^bold>\<not> (F1 \<^bold>\<rightarrow> F2) \<in> S \<longrightarrow> F1 \<in> S \<and> \<^bold>\<not> F2 \<in> S"
      using assms(1) by (rule Hintikka_l9)
    then have C:"F1 \<in> S \<and> \<^bold>\<not> F2 \<in> S"
      using \<open>\<^bold>\<not> (F1 \<^bold>\<rightarrow> F2) \<in> S\<close> by (rule mp)
    then have "F1 \<in> S"
      by (rule conjunct1)
    have "F1 \<in> S \<longrightarrow> isModel (interpretacionAsoc S) F1"
      using assms(2) by (rule conjunct1)
    then have "isModel (interpretacionAsoc S) F1"
      using \<open>F1 \<in> S\<close> by (rule mp)
    then have "(interpretacionAsoc S) \<Turnstile> F1"
      by (simp only: isModel_def)
    have "\<^bold>\<not> F2 \<in> S"
      using C by (rule conjunct2)
    have "\<^bold>\<not> F2 \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) F2"
      using assms(3) by (rule conjunct2)
    then have "\<not> isModel (interpretacionAsoc S) F2"
      using \<open>\<^bold>\<not> F2 \<in> S\<close> by (rule mp)
    then have N1:"\<not> (interpretacionAsoc S) \<Turnstile> F2"
      by (simp add: isModel_def) (*Pendiente*)
    have "\<not> ((interpretacionAsoc S) \<Turnstile> F1 \<longrightarrow> (interpretacionAsoc S) \<Turnstile> F2)"
    proof (rule ccontr)
      assume "\<not>\<not> ((interpretacionAsoc S) \<Turnstile> F1 \<longrightarrow> (interpretacionAsoc S) \<Turnstile> F2)"
      then have "(interpretacionAsoc S) \<Turnstile> F1 \<longrightarrow> (interpretacionAsoc S) \<Turnstile> F2"
        by simp (*Pendiente*)
      then have N2:"(interpretacionAsoc S) \<Turnstile> F2"
        using \<open>(interpretacionAsoc S) \<Turnstile> F1\<close> by (rule mp)
      show "False" 
        using N1 N2 by (rule notE)
    qed
    then have "\<not> (interpretacionAsoc S) \<Turnstile> (F1 \<^bold>\<rightarrow> F2)"
      by simp (*Pendiente (simp only: formula_semantics.simps(6))*)
    thus "\<not> isModel (interpretacionAsoc S) (F1 \<^bold>\<rightarrow> F2)"
      by (simp add: isModel_def) (*Pendiente*)
  qed
qed

lemma Hl2_5:
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
  shows "(F \<in> S \<longrightarrow> isModel (interpretacionAsoc S) F)
           \<and> (\<^bold>\<not> F \<in> S \<longrightarrow> (\<not>(isModel (interpretacionAsoc S) F)))"
proof (induct F)
  fix x
  show "(Atom x \<in> S \<longrightarrow> isModel (interpretacionAsoc S) (Atom x)) \<and>
         (\<^bold>\<not> (Atom x) \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) (Atom x))"
    using assms by (rule Hl2_1)
next
  show " (\<bottom> \<in> S \<longrightarrow> isModel (interpretacionAsoc S) \<bottom>) \<and>
    (\<^bold>\<not> \<bottom> \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) \<bottom>)" 
  proof (rule conjI)
    show "\<bottom> \<in> S \<longrightarrow> isModel (interpretacionAsoc S) \<bottom>"
    proof (rule impI)
      assume "\<bottom> \<in> S"
      have "\<bottom> \<notin> S" 
        using assms by (rule Hintikka_l1)
      thus "isModel (interpretacionAsoc S) \<bottom>"
        using \<open>\<bottom> \<in> S\<close> by (rule notE)
    qed
  next
    show "\<^bold>\<not> \<bottom> \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) \<bottom>"
    proof (rule impI)
      assume "\<^bold>\<not> \<bottom> \<in> S"
      have "\<bottom> \<notin> S"
        using assms by (rule Hintikka_l1)
      then have "\<not> (interpretacionAsoc S) \<Turnstile> \<bottom>"
        by simp (*Pendiente*)
      thus "\<not> isModel (interpretacionAsoc S) \<bottom>"
        by (simp add: isModel_def) (*Pendiente*)
    qed
  qed
    (*by (simp add: Hintikka_l1 assms isModel_def)*) (*Pendiente*)
next
  fix F
  show "(F \<in> S \<longrightarrow> isModel (interpretacionAsoc S) F) \<and>
         (\<^bold>\<not> F \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) F) \<Longrightarrow>
         (\<^bold>\<not> F \<in> S \<longrightarrow> isModel (interpretacionAsoc S) (\<^bold>\<not> F)) \<and>
         (\<^bold>\<not> (\<^bold>\<not> F) \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) (\<^bold>\<not> F))"
    using assms by (rule Hl2_2)
next
  fix F1 F2
  show "(F1 \<in> S \<longrightarrow> isModel (interpretacionAsoc S) F1) \<and>
       (\<^bold>\<not> F1 \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) F1) \<Longrightarrow>
       (F2 \<in> S \<longrightarrow> isModel (interpretacionAsoc S) F2) \<and>
       (\<^bold>\<not> F2 \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) F2) \<Longrightarrow>
       (F1 \<^bold>\<and> F2 \<in> S \<longrightarrow> isModel (interpretacionAsoc S) (F1 \<^bold>\<and> F2)) \<and>
       (\<^bold>\<not> (F1 \<^bold>\<and> F2) \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) (F1 \<^bold>\<and> F2))"
    using assms by (rule Hl2_3)
next
  fix F1 F2
  show "(F1 \<in> S \<longrightarrow> isModel (interpretacionAsoc S) F1) \<and>
       (\<^bold>\<not> F1 \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) F1) \<Longrightarrow>
       (F2 \<in> S \<longrightarrow> isModel (interpretacionAsoc S) F2) \<and>
       (\<^bold>\<not> F2 \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) F2) \<Longrightarrow>
       (F1 \<^bold>\<or> F2 \<in> S \<longrightarrow> isModel (interpretacionAsoc S) (F1 \<^bold>\<or> F2)) \<and>
       (\<^bold>\<not> (F1 \<^bold>\<or> F2) \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) (F1 \<^bold>\<or> F2))"
    using assms by (rule Hl2_4)
next
  fix F1 F2
  show "(F1 \<in> S \<longrightarrow> isModel (interpretacionAsoc S) F1) \<and>
       (\<^bold>\<not> F1 \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) F1) \<Longrightarrow>
       (F2 \<in> S \<longrightarrow> isModel (interpretacionAsoc S) F2) \<and>
       (\<^bold>\<not> F2 \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) F2) \<Longrightarrow>
       (F1 \<^bold>\<rightarrow> F2 \<in> S \<longrightarrow> isModel (interpretacionAsoc S) (F1 \<^bold>\<rightarrow> F2)) \<and>
       (\<^bold>\<not> (F1 \<^bold>\<rightarrow> F2) \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) (F1 \<^bold>\<rightarrow> F2))"
    using assms by (rule Hl2_5)
qed

lemma Hintikka_modelo:
  assumes "Hintikka S"
  shows "isModelSet (interpretacionAsoc S) S"
proof-
  have "\<forall>F. (F\<in> S \<longrightarrow> isModel (interpretacionAsoc S) F)"
  proof (rule allI)
    fix F
    have "(F \<in> S \<longrightarrow> isModel (interpretacionAsoc S) F)
           \<and> (\<^bold>\<not> F \<in> S \<longrightarrow> (\<not>(isModel (interpretacionAsoc S) F)))"
      using assms by (rule Hintikkas_lemma_l2)
    thus "F \<in> S \<longrightarrow> isModel (interpretacionAsoc S) F"
      by (rule conjunct1)
  qed
  thus "isModelSet (interpretacionAsoc S) S"
    by (simp only: modelSet)
qed 

text \<open>\comentario{Buscar qué lema es satAlt.}\<close>

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