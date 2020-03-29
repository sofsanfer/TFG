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

lemma Hintikka_l10_atom: 
  assumes "Hintikka S" 
  shows "\<^bold>\<not> (Atom x) \<in> S \<longrightarrow> (Atom x) \<notin> S"
proof -
  have "Atom x \<in> S \<longrightarrow> \<^bold>\<not> (Atom x) \<notin> S"
    using assms by (rule Hintikka_l2)
  then have "\<not> (\<^bold>\<not> (Atom x) \<notin> S) \<longrightarrow> \<not> (Atom x \<in> S)"
    by (rule not_mono)
  then have "\<not>\<not>(\<^bold>\<not> (Atom x) \<in> S) \<longrightarrow> Atom x \<notin> S"
    by this
  thus ?thesis using 
    by simp (*Pendiente - rule notnotD*)
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
  assume H:"\<^bold>\<not> (\<^bold>\<not> F) \<in> S"
  have "\<^bold>\<not> (\<^bold>\<not> F) \<in> S \<longrightarrow> F \<in> S"
    using assms(1) by (rule Hintikka_l6)
  then have I:"F \<in> S"
    using H by (rule mp)
  have "\<not> (F \<notin> S) \<longrightarrow> \<not>(\<^bold>\<not> F \<in> S)"
    using assms(2) by (rule not_mono)
  then have "F \<in> S \<longrightarrow> \<^bold>\<not> F \<notin> S"
    by simp (*Pendiente*)
  thus "\<^bold>\<not> F \<notin> S"
    using I by (rule mp)
qed

lemma Hintikka_l10_and: 
  assumes "Hintikka S" 
          "\<^bold>\<not> G \<in> S \<longrightarrow> G \<notin> S"
          "\<^bold>\<not> H \<in> S \<longrightarrow> H \<notin> S"
  shows "\<^bold>\<not> (G \<^bold>\<and> H) \<in> S \<longrightarrow> (G \<^bold>\<and> H) \<notin> S"
proof (rule impI)
  assume H:"\<^bold>\<not> (G \<^bold>\<and> H) \<in> S"
  have "\<^bold>\<not> (G \<^bold>\<and> H) \<in> S \<longrightarrow> (\<^bold>\<not> G \<in> S \<or> \<^bold>\<not> H \<in> S)"
    using assms(1) by (rule Hintikka_l7)
  then have "\<^bold>\<not> G \<in> S \<or> \<^bold>\<not> H \<in> S"
    using H by (rule mp)
  then show "(G \<^bold>\<and> H) \<notin> S"
  proof (rule disjE)
    assume H1:"\<^bold>\<not> G \<in> S"
    have "G \<notin> S"
      using assms(2) H1 by (rule mp)
    then have I1:"\<not> (G \<in> S \<and> H \<in> S)" 
      by simp (*Pendiente*)
    have "(G \<^bold>\<and> H \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S)"
      using assms(1) by (rule Hintikka_l3)
    then have "\<not>(G \<in> S \<and> H \<in> S) \<longrightarrow> \<not>(G \<^bold>\<and> H \<in> S)"
      by (rule not_mono)
    thus "G \<^bold>\<and> H \<notin> S"
      using I1 by (rule mp)
  next
    assume H2:"\<^bold>\<not> H \<in> S"
    have "H \<notin> S"
      using assms(3) H2 by (rule mp)
    then have I2:"\<not> (G \<in> S \<and> H \<in> S)" 
      by simp (*Pendiente*)
    have "(G \<^bold>\<and> H \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S)"
      using assms(1) by (rule Hintikka_l3)
    then have "\<not>(G \<in> S \<and> H \<in> S) \<longrightarrow> \<not>(G \<^bold>\<and> H \<in> S)"
      by (rule not_mono)
    thus "G \<^bold>\<and> H \<notin> S"
      using I2 by (rule mp)
  qed
qed

lemma Hintikka_l10_or: 
  assumes "Hintikka S" 
          "\<^bold>\<not> G \<in> S \<longrightarrow> G \<notin> S"
          "\<^bold>\<not> H \<in> S \<longrightarrow> H \<notin> S"
  shows "\<^bold>\<not> (G \<^bold>\<or> H) \<in> S \<longrightarrow> (G \<^bold>\<or> H) \<notin> S"
proof (rule impI)
  assume H:"\<^bold>\<not> (G \<^bold>\<or> H) \<in> S"
  have "\<^bold>\<not> (G \<^bold>\<or> H) \<in> S \<longrightarrow> (\<^bold>\<not> G \<in> S \<and> \<^bold>\<not> H \<in> S)"
    using assms(1) by (rule Hintikka_l8)
  then have C:"\<^bold>\<not> G \<in> S \<and> \<^bold>\<not> H \<in> S"
    using H by (rule mp)
  then have C1:"\<^bold>\<not> G \<in> S"
    by (rule conjunct1)
  have C2:"\<^bold>\<not> H \<in> S"
    using C by (rule conjunct2)
  have NC1:"G \<notin> S" 
    using assms(2) C1 by (rule mp)
  have NC2:"H \<notin> S" 
    using assms(3) C2 by (rule mp)
  have I:"\<not> (G \<in> S \<or> H \<in> S)"
    using NC1 NC2 by simp (*Pendiente*)
  have "(G \<^bold>\<or> H \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S)"
    using assms(1) by (rule Hintikka_l4)
  then have "\<not> (G \<in> S \<or> H \<in> S) \<longrightarrow> \<not> (G \<^bold>\<or> H \<in> S)"
    by (rule not_mono)
  thus "G \<^bold>\<or> H \<notin> S"
    using I by (rule mp)
qed

lemma Hintikka_l10_imp: 
  assumes "Hintikka S" 
          "\<^bold>\<not> G \<in> S \<longrightarrow> G \<notin> S"
          "\<^bold>\<not> H \<in> S \<longrightarrow> H \<notin> S"
  shows "\<^bold>\<not> (G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> (G \<^bold>\<rightarrow> H) \<notin> S"
proof (rule impI)
  assume H:"\<^bold>\<not> (G \<^bold>\<rightarrow> H) \<in> S"
  have "\<^bold>\<not> (G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> (G \<in> S \<and> \<^bold>\<not> H \<in> S)"
    using assms(1) by (rule Hintikka_l9)
  then have C:"G \<in> S \<and> \<^bold>\<not> H \<in> S"
    using H by (rule mp)
  then have C1:"G \<in> S"
    by (rule conjunct1)
  have C2:"\<^bold>\<not> H \<in> S"
    using C by (rule conjunct2)
  have "H \<notin> S"
    using assms(3) C2 by (rule mp)
  oops

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