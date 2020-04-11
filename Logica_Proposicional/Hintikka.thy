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
    by (iprover intro: conjunct2 conjunct1) (*?*)
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
  then have "\<forall>F G. F \<^bold>\<or> G \<in> S \<longrightarrow> F \<in> S \<or> G \<in> S"
    by (iprover intro: conjunct2 conjunct1) (*?*)
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
  then have "\<forall>F G. F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> \<^bold>\<not>F \<in> S \<or> G \<in> S"
    by (iprover intro: conjunct2 conjunct1) (*?*)
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
  then have "\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<in> S"
    by (iprover intro: conjunct2 conjunct1) (*?*)
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
  then have "\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S"
    by (iprover intro: conjunct2 conjunct1) (*?*)
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
  then have "\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S"
    by (iprover intro: conjunct2 conjunct1) (*?*)
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
  then have "\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S"
    by (iprover intro: conjunct2) (*?*)
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

text \<open>\comentario{DUDA: no me carga al usarn(simp only: ... ) al
  al reiterar el uso de la regla conjunct2. Además, tampoco me carga con
  intro, creo que no entiendo cómo funciona. Me funciona añadiendo el
  método de demostración iprover delante, pero no sin usarlo.}\<close>

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

lemma notnotI: "P \<Longrightarrow> \<not>\<not> P"
  by auto

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

lemma Hintikka_l10_and: 
  assumes "Hintikka S \<Longrightarrow> \<^bold>\<not> G \<in> S \<longrightarrow> G \<notin> S"
          "Hintikka S \<Longrightarrow> \<^bold>\<not> H \<in> S \<longrightarrow> H \<notin> S"
          "Hintikka S"
  shows "\<^bold>\<not> (G \<^bold>\<and> H) \<in> S \<longrightarrow> (G \<^bold>\<and> H) \<notin> S"
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

lemma Hintikka_l10_or: 
  assumes "Hintikka S \<Longrightarrow> \<^bold>\<not> G \<in> S \<longrightarrow> G \<notin> S"
          "Hintikka S \<Longrightarrow> \<^bold>\<not> H \<in> S \<longrightarrow> H \<notin> S"
          "Hintikka S"
  shows "\<^bold>\<not> (G \<^bold>\<or> H) \<in> S \<longrightarrow> (G \<^bold>\<or> H) \<notin> S"
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
  shows "\<^bold>\<not> (G \<^bold>\<rightarrow> H) \<in> S \<longrightarrow> (G \<^bold>\<rightarrow> H) \<notin> S"
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

lemma Hintikka_l10_detallada: 
  "Hintikka S \<Longrightarrow> \<^bold>\<not> F \<in> S \<longrightarrow> F \<notin> S"
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
proof (rule conjI)
  show "\<And>x. Atom x \<in> S \<longrightarrow> isModel (interpretacionAsoc S) (Atom x)" 
  proof (rule impI)
    fix x
    assume "Atom x \<in> S"
    hence "(interpretacionAsoc S) x"
      by (simp only: interpretacionAsoc_def)
    hence "interpretacionAsoc S \<Turnstile> Atom x"
      by (simp only: formula_semantics.simps(1))
    thus "isModel (interpretacionAsoc S) (Atom x)"
      by (simp only: isModel_def)
  qed
next 
  show 
  "\<And>x. \<^bold>\<not> (Atom x) \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) (Atom x)" 
  proof (rule impI)
    fix x
    assume "\<^bold>\<not> (Atom x) \<in> S" 
    have "\<^bold>\<not> (Atom x) \<in> S \<longrightarrow> Atom x \<notin> S"
      using assms by (rule Hintikka_l10)
    then have "Atom x \<notin> S"
      using \<open>\<^bold>\<not> (Atom x) \<in> S\<close> by (rule mp)
    have IntEq1:"Atom x \<in> S = (interpretacionAsoc S) x"
      by (simp only: interpretacionAsoc_def)
    then have "\<not> ((interpretacionAsoc S) x)"
      using \<open>\<not> (Atom x \<in> S)\<close> by (rule subst)
    have IntEq2:"(interpretacionAsoc S) x = (interpretacionAsoc S) \<Turnstile> (Atom x)"
      by (simp only: formula_semantics.simps(1))
    then have "\<not> ((interpretacionAsoc S) \<Turnstile> (Atom x))"
      using \<open>\<not> ((interpretacionAsoc S) x)\<close> by (rule subst)
    thus "\<not> isModel (interpretacionAsoc S) (Atom x)" 
      by (simp add: isModel_def) (*Pendiente*)
  qed
qed

lemma Hl2_1:
  assumes  "Hintikka S"
  shows "\<And>x. (Atom x \<in> S \<longrightarrow> isModel (interpretacionAsoc S) (Atom x)) \<and>
         (\<^bold>\<not> (Atom x) \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) (Atom x))"
  by (simp add: Hintikka_l10 assms isModel_def interpretacionAsoc_def) 

lemma negDef:
  assumes "(\<not> isModel (interpretacionAsoc S) F)" 
  shows "(\<not> (interpretacionAsoc S) \<Turnstile> F)"
proof -
  have "isModel (interpretacionAsoc S) F = (interpretacionAsoc S) \<Turnstile> F"
    by (simp only: isModel_def)
  then have "(\<not> isModel (interpretacionAsoc S) F) = 
 (\<not> (interpretacionAsoc S) \<Turnstile> F)" 
    by (rule arg_cong)
  thus ?thesis 
    using assms by simp (*Pendiente*)
qed

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
    then have "(\<not> isModel (interpretacionAsoc S) F)"
      using  \<open>\<^bold>\<not> F \<in> S\<close> by (rule mp)
    then have "\<not> (interpretacionAsoc S) \<Turnstile> F"
      by (rule negDef)
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
        by (rule negDef)
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
        by (rule negDef)
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
      by (rule negDef)
    have "\<^bold>\<not> F2 \<in> S"
      using C by (rule conjunct2)
    have "\<^bold>\<not> F2 \<in> S \<longrightarrow> \<not> isModel (interpretacionAsoc S) F2"
      using assms(3) by (rule conjunct2)
    then have "\<not> isModel (interpretacionAsoc S) F2"
      using \<open>\<^bold>\<not> F2 \<in> S\<close> by (rule mp)
    then have D2:"\<not> (interpretacionAsoc S) \<Turnstile> F2"
      by (rule negDef)
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
        by (rule negDef)
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
      by (rule negDef)
    have "\<not> ((interpretacionAsoc S) \<Turnstile> F1 \<longrightarrow> (interpretacionAsoc S) \<Turnstile> F2)"
    proof (rule ccontr)
      assume "\<not>\<not> ((interpretacionAsoc S) \<Turnstile> F1 \<longrightarrow> (interpretacionAsoc S) \<Turnstile> F2)"
      then have "(interpretacionAsoc S) \<Turnstile> F1 \<longrightarrow> (interpretacionAsoc S) \<Turnstile> F2"
        by (rule notnotD)
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
proof -
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