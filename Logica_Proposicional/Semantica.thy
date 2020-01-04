(*<*) 
theory Semantica
  imports 
    Sintaxis
begin
(*>*)

section \<open>Semántica\<close>

text \<open>\comentario{Escribir la definición de interpretación como una
  aplicación de los símbolos proposicionales (o átomos) en los valores 
  de verdad}\<close> 

type_synonym 'a valuation = "'a \<Rightarrow> bool"

text \<open>\comentario{Definir el valor de una fórmula proposicional en una
  interpretación (la def. es por recursión en la estructura de la 
  fórmula)}\<close>

primrec formula_semantics :: 
  "'a valuation \<Rightarrow> 'a formula \<Rightarrow> bool" (infix "\<Turnstile>" 51) where
  "\<A> \<Turnstile> Atom k = \<A> k" 
| "\<A> \<Turnstile> \<bottom> = False" 
| "\<A> \<Turnstile> Not F = (\<not> \<A> \<Turnstile> F)" 
| "\<A> \<Turnstile> And F G = (\<A> \<Turnstile> F \<and> \<A> \<Turnstile> G)" 
| "\<A> \<Turnstile> Or F G = (\<A> \<Turnstile> F \<or> \<A> \<Turnstile> G)" 
| "\<A> \<Turnstile> Imp F G = (\<A> \<Turnstile> F \<longrightarrow> \<A> \<Turnstile> G)"

text \<open>\comentario{Definir fórmula válida (o tautología).}\<close>

abbreviation valid ("\<Turnstile> _" 51) where
  "\<Turnstile> F \<equiv> \<forall>A. A \<Turnstile> F"

text \<open>\comentario{Enunciar y hacer la demostración detallada de 
  irrelevant-atom-atomica.}\<close>

lemma irrelevant_atom_atomica_l1:
  assumes "A \<notin> atoms (Atom x)" 
  shows "x \<noteq> A"
proof (rule notI)
  assume "x = A"
  then have "A \<in> {x}" 
    by (simp only: singleton_iff)
  also have "\<dots> = atoms (Atom x)"
    by (simp only: formula.set(1))
  finally have "A \<in> atoms (Atom x)"
    by this 
  with assms show "False"  
    by (rule notE)
qed

lemma irrelevant_atom_atomica:
  assumes "A \<notin> atoms (Atom x)" 
  shows "(\<A>(A := V)) \<Turnstile> (Atom x) \<longleftrightarrow> \<A> \<Turnstile> (Atom x)"
proof -
  have "x \<noteq> A"
    using assms
    by (rule irrelevant_atom_atomica_l1)
  have "(\<A>(A := V)) \<Turnstile> (Atom x) = (\<A>(A := V)) x"
    by (simp only: formula_semantics.simps(1))
  also have "\<dots> = \<A> x"
    using \<open>x \<noteq> A\<close>
    by (rule fun_upd_other)
  also have "\<dots> = \<A> \<Turnstile> (Atom x)"
    by (simp only: formula_semantics.simps(1))
  finally show ?thesis
    by this
qed

lemma irrelevant_atom_bot:
  assumes "A \<notin> atoms \<bottom>" 
  shows "(\<A>(A := V)) \<Turnstile> \<bottom> \<longleftrightarrow> \<A> \<Turnstile> \<bottom>"
  by (simp only: formula_semantics.simps(2))

lemma irrelevant_atom_not_l1:
  assumes "A \<notin> atoms (\<^bold>\<not> F)"
  shows   "A \<notin> atoms F"
proof
  assume "A \<in> atoms F"
  then have "A \<in> atoms (\<^bold>\<not> F)"
    by (simp only: formula.set(3)) 
  with assms show False
    by (rule notE)
qed

lemma irrelevant_atom_not:
  assumes "A \<notin> atoms F \<Longrightarrow> \<A>(A := V) \<Turnstile> F \<longleftrightarrow> \<A> \<Turnstile> F"
          "A \<notin> atoms (\<^bold>\<not> F)"
 shows "\<A>(A := V) \<Turnstile> \<^bold>\<not> F \<longleftrightarrow> \<A> \<Turnstile> \<^bold>\<not> F"
proof -
  have "A \<notin> atoms F"
    using assms(2) by (rule irrelevant_atom_not_l1)
  then have "\<A>(A := V) \<Turnstile> F \<longleftrightarrow> \<A> \<Turnstile> F"
    by (rule assms(1))
  have "\<A>(A := V) \<Turnstile> \<^bold>\<not> F = (\<not> \<A>(A := V) \<Turnstile> F)"
    by (simp only: formula_semantics.simps(3))
  also have "\<dots> = (\<not> \<A> \<Turnstile> F)"
    by (simp only: \<open>\<A>(A := V) \<Turnstile> F \<longleftrightarrow> \<A> \<Turnstile> F\<close>)
  also have "\<dots> = \<A> \<Turnstile> \<^bold>\<not> F"
    by (simp only: formula_semantics.simps(3))
  finally show "\<A>(A := V) \<Turnstile> \<^bold>\<not> F \<longleftrightarrow> \<A> \<Turnstile> \<^bold>\<not> F"
    by this
qed

lemma irrelevant_atom_and_l1:
  assumes "A \<notin> atoms (F \<^bold>\<and> G)"
  shows   "A \<notin> atoms F"
proof 
  assume "A \<in> atoms F"
  then have "A \<in> atoms F \<union> atoms G"
    by (rule UnI1)
  then have "A \<in> atoms (F \<^bold>\<and> G)"
    by (simp only: formula.set(4))
  with assms show False 
    by (rule notE)
qed

lemma irrelevant_atom_and_l2:
  assumes "A \<notin> atoms (F \<^bold>\<and> G)"
  shows   "A \<notin> atoms G"
proof 
  assume "A \<in> atoms G"
  then have "A \<in> atoms F \<union> atoms G"
    by (rule UnI2)
  then have "A \<in> atoms (F \<^bold>\<and> G)"
    by (simp only: formula.set(4))
  with assms show False 
    by (rule notE)
qed

lemma irrelevant_atom_and:
  assumes "A \<notin> atoms F \<Longrightarrow> \<A>(A := V) \<Turnstile> F \<longleftrightarrow> \<A> \<Turnstile> F"
          "A \<notin> atoms G \<Longrightarrow> \<A>(A := V) \<Turnstile> G \<longleftrightarrow> \<A> \<Turnstile> G"
          "A \<notin> atoms (F \<^bold>\<and> G)"
  shows "\<A>(A := V) \<Turnstile> (F \<^bold>\<and> G) \<longleftrightarrow> \<A> \<Turnstile> (F \<^bold>\<and> G)"
proof -
  have "A \<notin> atoms F"
    using assms(3)
    by (rule irrelevant_atom_and_l1)
  then have HF: "\<A>(A := V) \<Turnstile> F \<longleftrightarrow> \<A> \<Turnstile> F"
    by (rule assms(1))
  have "A \<notin> atoms G"
    using assms(3)
    by (rule irrelevant_atom_and_l2)
  then have HG: "\<A>(A := V) \<Turnstile> G \<longleftrightarrow> \<A> \<Turnstile> G"
    by (rule assms(2))
  have "\<A>(A := V) \<Turnstile> (F \<^bold>\<and> G) = (\<A>(A := V) \<Turnstile> F \<and> \<A>(A := V) \<Turnstile> G)"
    by (simp only: formula_semantics.simps(4))
  also have "\<dots> = (\<A> \<Turnstile> F \<and> \<A> \<Turnstile> G)"
    by (simp only: HF HG)
  also have "\<dots> = \<A> \<Turnstile> (F \<^bold>\<and> G)"
    by (simp only: formula_semantics.simps(4))
  finally show "\<A>(A := V) \<Turnstile> (F \<^bold>\<and> G) \<longleftrightarrow> \<A> \<Turnstile> (F \<^bold>\<and> G)"
    by this
qed

lemma irrelevant_atom_or_l1:
  assumes "A \<notin> atoms (F \<^bold>\<or> G)"
  shows   "A \<notin> atoms F"
proof 
  assume "A \<in> atoms F"
  then have "A \<in> atoms F \<union> atoms G"
    by (rule UnI1)
  then have "A \<in> atoms (F \<^bold>\<or> G)"
    by (simp only: formula.set(5))
  with assms show False 
    by (rule notE)
qed

lemma irrelevant_atom_or_l2:
  assumes "A \<notin> atoms (F \<^bold>\<or> G)"
  shows   "A \<notin> atoms G"
proof 
  assume "A \<in> atoms G"
  then have "A \<in> atoms F \<union> atoms G"
    by (rule UnI2)
  then have "A \<in> atoms (F \<^bold>\<or> G)"
    by (simp only: formula.set(5))
  with assms show False 
    by (rule notE)
qed

lemma irrelevant_atom_or:
  assumes "A \<notin> atoms F \<Longrightarrow> \<A>(A := V) \<Turnstile> F \<longleftrightarrow> \<A> \<Turnstile> F"
          "A \<notin> atoms G \<Longrightarrow> \<A>(A := V) \<Turnstile> G \<longleftrightarrow> \<A> \<Turnstile> G"
          "A \<notin> atoms (F \<^bold>\<or> G)"
  shows   "\<A>(A := V) \<Turnstile> (F \<^bold>\<or> G) \<longleftrightarrow> \<A> \<Turnstile> (F \<^bold>\<or> G)"
proof -
  have "A \<notin> atoms F"
    using assms(3)
    by (rule irrelevant_atom_or_l1)
  then have HF: "\<A>(A := V) \<Turnstile> F \<longleftrightarrow> \<A> \<Turnstile> F"
    by (rule assms(1))
  have "A \<notin> atoms G"
    using assms(3)
    by (rule irrelevant_atom_or_l2)
  then have HG: "\<A>(A := V) \<Turnstile> G \<longleftrightarrow> \<A> \<Turnstile> G"
    by (rule assms(2))
  have "\<A>(A := V) \<Turnstile> (F \<^bold>\<or> G) = (\<A>(A := V) \<Turnstile> F \<or> \<A>(A := V) \<Turnstile> G)"
    by (simp only: formula_semantics.simps(5))
  also have "\<dots> = (\<A> \<Turnstile> F \<or> \<A> \<Turnstile> G)"
    by (simp only: HF HG)
  also have "\<dots> = \<A> \<Turnstile> (F \<^bold>\<or> G)"
    by (simp only: formula_semantics.simps(5))
  finally show "\<A>(A := V) \<Turnstile> (F \<^bold>\<or> G) \<longleftrightarrow> \<A> \<Turnstile> (F \<^bold>\<or> G)"
    by this
qed

lemma irrelevant_atom_imp_l1:
  assumes "A \<notin> atoms (F \<^bold>\<rightarrow> G)"
  shows   "A \<notin> atoms F"
proof 
  assume "A \<in> atoms F"
  then have "A \<in> atoms F \<union> atoms G"
    by (rule UnI1)
  then have "A \<in> atoms (F \<^bold>\<rightarrow> G)"
    by (simp only: formula.set(6))
  with assms show False 
    by (rule notE)
qed

lemma irrelevant_atom_imp_l2:
  assumes "A \<notin> atoms (F \<^bold>\<rightarrow> G)"
  shows   "A \<notin> atoms G"
proof 
  assume "A \<in> atoms G"
  then have "A \<in> atoms F \<union> atoms G"
    by (rule UnI2)
  then have "A \<in> atoms (F \<^bold>\<rightarrow> G)"
    by (simp only: formula.set(6))
  with assms show False 
    by (rule notE)
qed

lemma irrelevant_atom_imp:
  assumes "A \<notin> atoms F \<Longrightarrow> \<A>(A := V) \<Turnstile> F \<longleftrightarrow> \<A> \<Turnstile> F"
          "A \<notin> atoms G \<Longrightarrow> \<A>(A := V) \<Turnstile> G \<longleftrightarrow> \<A> \<Turnstile> G"
          "A \<notin> atoms (F \<^bold>\<rightarrow> G)"
  shows "\<A>(A := V) \<Turnstile> (F \<^bold>\<rightarrow> G) \<longleftrightarrow> \<A> \<Turnstile> (F \<^bold>\<rightarrow> G)"
proof -
  have "A \<notin> atoms F"
    using assms(3)
    by (rule irrelevant_atom_imp_l1)
  then have HF: "\<A>(A := V) \<Turnstile> F \<longleftrightarrow> \<A> \<Turnstile> F"
    by (rule assms(1))
  have "A \<notin> atoms G"
    using assms(3)
    by (rule irrelevant_atom_imp_l2)
  then have HG: "\<A>(A := V) \<Turnstile> G \<longleftrightarrow> \<A> \<Turnstile> G"
    by (rule assms(2))
  have "\<A>(A := V) \<Turnstile> (F \<^bold>\<rightarrow> G) = (\<A>(A := V) \<Turnstile> F \<longrightarrow> \<A>(A := V) \<Turnstile> G)"
    by (simp only: formula_semantics.simps(6))
  also have "\<dots> = (\<A> \<Turnstile> F \<longrightarrow> \<A> \<Turnstile> G)"
    by (simp only: HF HG)
  also have "\<dots> = \<A> \<Turnstile> (F \<^bold>\<rightarrow> G)"
    by (simp only: formula_semantics.simps(6))
  finally show "\<A>(A := V) \<Turnstile> (F \<^bold>\<rightarrow> G) \<longleftrightarrow> \<A> \<Turnstile> (F \<^bold>\<rightarrow> G)"
    by this
qed

lemma irrelevant_atom_detallada:
  "A \<notin> atoms F \<Longrightarrow> (\<A>(A := V)) \<Turnstile> F \<longleftrightarrow> \<A> \<Turnstile> F"
proof (induction F)
  case (Atom x)
  then show ?case by (rule irrelevant_atom_atomica)
next
  case Bot
  then show ?case by (rule irrelevant_atom_bot)
next
  case (Not F)
  then show ?case by (rule irrelevant_atom_not)
next
  case (And F1 F2)
  then show ?case by (rule irrelevant_atom_and)
next
  case (Or F1 F2)
  then show ?case by (rule irrelevant_atom_or)
next
  case (Imp F1 F2)
  then show ?case by (rule irrelevant_atom_imp)
qed

lemma irrelevant_atom: 
  "A \<notin> atoms F \<Longrightarrow> (\<A>(A := V)) \<Turnstile> F \<longleftrightarrow> \<A> \<Turnstile> F"
  by (induction F) simp_all

text\<open>Lema: enunciar y hacer la demostración detallada.\<close>

lemma relevant_atoms_same_semantics_atomica: 
  assumes "\<forall>k \<in> atoms (Atom x). \<A>\<^sub>1 k = \<A>\<^sub>2 k"
  shows "\<A>\<^sub>1 \<Turnstile> (Atom x) \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> (Atom x)"
proof (rule iffI)
  assume "\<A>\<^sub>1 \<Turnstile> (Atom x)"
  then have "\<A>\<^sub>1 x"
    by (simp only: formula_semantics.simps(1))
  then have "\<A>\<^sub>2 x" using assms 
    by simp (* Pendiente *)
  thus "\<A>\<^sub>2 \<Turnstile> (Atom x)"
    by (simp only: formula_semantics.simps(1))
next
  assume "\<A>\<^sub>2 \<Turnstile> (Atom x)"
  then have "\<A>\<^sub>2 x"
    by (simp only: formula_semantics.simps(1))
  then have "\<A>\<^sub>1 x" using assms 
    by simp (* Pendiente *)
  thus "\<A>\<^sub>1 \<Turnstile> (Atom x)"
    by (simp only: formula_semantics.simps(1))
qed

lemma relevant_atoms_same_semantics_bot: 
  assumes "\<forall>k \<in> atoms \<bottom>. \<A>\<^sub>1 k = \<A>\<^sub>2 k"
  shows "\<A>\<^sub>1 \<Turnstile> \<bottom> \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> \<bottom>"
proof (rule iffI)
  assume "\<A>\<^sub>1 \<Turnstile> \<bottom>"
  then have "False"
    by (simp only: formula_semantics.simps(2))
  then show "\<A>\<^sub>2 \<Turnstile> \<bottom>"
    by (simp only: formula_semantics.simps(2))
next
  assume "\<A>\<^sub>2 \<Turnstile> \<bottom>"
  then have "False"
    by (simp only: formula_semantics.simps(2))
  then show "\<A>\<^sub>1 \<Turnstile> \<bottom>"
    by (simp only: formula_semantics.simps(2))
qed

lemma relevant_atoms_same_semantics_not: 
  assumes "\<forall>k \<in> atoms F. \<A>\<^sub>1 k = \<A>\<^sub>2 k \<Longrightarrow> \<A>\<^sub>1 \<Turnstile> F \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> F"
          "\<forall>k \<in> atoms (\<^bold>\<not> F). \<A>\<^sub>1 k = \<A>\<^sub>2 k"
        shows "\<A>\<^sub>1 \<Turnstile> (\<^bold>\<not> F) \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> (\<^bold>\<not> F)"
proof (rule iffI)
  assume "\<A>\<^sub>1 \<Turnstile> (\<^bold>\<not> F)"
  then have H1:"\<not> (\<A>\<^sub>1 \<Turnstile> F)"
    by simp (*Da error?: (simp only: formula_semantics.simps(3))*)
  have "\<forall>k \<in> atoms F. \<A>\<^sub>1 k = \<A>\<^sub>2 k" using assms(2)
    by (simp only: formula.set(3))
  then have "\<A>\<^sub>1 \<Turnstile> F \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> F"
    by (simp only: assms(1))
  then have "\<A>\<^sub>2 \<Turnstile> F \<longrightarrow> \<A>\<^sub>1 \<Turnstile> F"
    by simp (* Pendiente *)
  then have "\<not>(\<A>\<^sub>1 \<Turnstile> F) \<longrightarrow> \<not>(\<A>\<^sub>2 \<Turnstile> F)"
    by (rule not_mono)
  then have "\<not> (\<A>\<^sub>2 \<Turnstile> F)" using H1
    by (rule impE)
  thus "\<A>\<^sub>2 \<Turnstile> (\<^bold>\<not> F)"
    by simp (*(simp only: formula_semantics.simps(3))*)
next
  assume "\<A>\<^sub>2 \<Turnstile> (\<^bold>\<not> F)"
  then have H2:"\<not> (\<A>\<^sub>2 \<Turnstile> F)"
    by simp (*Da error?: (simp only: formula_semantics.simps(3))*)
  have "\<forall>k \<in> atoms F. \<A>\<^sub>1 k = \<A>\<^sub>2 k" using assms(2)
    by (simp only: formula.set(3))
  then have "\<A>\<^sub>1 \<Turnstile> F \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> F"
    by (simp only: assms(1))
  then have "\<A>\<^sub>1 \<Turnstile> F \<longrightarrow> \<A>\<^sub>2 \<Turnstile> F"
    by simp (* Pendiente *)
  then have "\<not>(\<A>\<^sub>2 \<Turnstile> F) \<longrightarrow> \<not>(\<A>\<^sub>1 \<Turnstile> F)"
    by (rule not_mono)
  then have "\<not> (\<A>\<^sub>1 \<Turnstile> F)" using H2
    by (rule impE)
  thus "\<A>\<^sub>1 \<Turnstile> (\<^bold>\<not> F)"
    by simp (*(simp only: formula_semantics.simps(3))*)
qed

lemma relevant_atoms_same_semantics_and: 
  assumes "\<forall>k \<in> atoms F. \<A>\<^sub>1 k = \<A>\<^sub>2 k \<Longrightarrow> \<A>\<^sub>1 \<Turnstile> F \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> F"
          "\<forall>k \<in> atoms G. \<A>\<^sub>1 k = \<A>\<^sub>2 k \<Longrightarrow> \<A>\<^sub>1 \<Turnstile> G \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> G"
          "\<forall>k \<in> atoms (F \<^bold>\<and> G). \<A>\<^sub>1 k = \<A>\<^sub>2 k"
        shows "\<A>\<^sub>1 \<Turnstile> (F \<^bold>\<and> G) \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> (F \<^bold>\<and> G)"
proof -
  have "\<forall>k \<in> atoms F. \<A>\<^sub>1 k = \<A>\<^sub>2 k" using assms(3)
    by simp (* Pendiente *)
  then have H1:"\<A>\<^sub>1 \<Turnstile> F \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> F" 
    by (simp only: assms(1))
  have "\<forall>k \<in> atoms G. \<A>\<^sub>1 k = \<A>\<^sub>2 k" using assms(3)
    by simp (* Pendiente *)
  then have H2:"\<A>\<^sub>1 \<Turnstile> G \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> G" 
    by (simp only: assms(2))
  show "\<A>\<^sub>1 \<Turnstile> (F \<^bold>\<and> G) \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> (F \<^bold>\<and> G)"
  proof (rule iffI)
    assume "\<A>\<^sub>1 \<Turnstile> (F \<^bold>\<and> G)"
    then have C:"\<A>\<^sub>1 \<Turnstile> F \<and> \<A>\<^sub>1 \<Turnstile> G" 
      by (simp only: formula_semantics.simps(4))
    then have C1:"\<A>\<^sub>1 \<Turnstile> F" 
      by (rule conjunct1)
    have F1:"\<A>\<^sub>2 \<Turnstile> F" using H1 C1
      by (rule iffD1)
    have C2:"\<A>\<^sub>1 \<Turnstile> G" using C
      by (rule conjunct2)
    have G1:"\<A>\<^sub>2 \<Turnstile> G" using H2 C2
      by (rule iffD1)
    have "\<A>\<^sub>2 \<Turnstile> F \<and> \<A>\<^sub>2 \<Turnstile> G" using F1 G1
      by (rule conjI)
    thus "\<A>\<^sub>2 \<Turnstile> (F \<^bold>\<and> G)"
      by (simp only: formula_semantics.simps(4))
  next
    assume "\<A>\<^sub>2 \<Turnstile> (F \<^bold>\<and> G)"
    then have C:"\<A>\<^sub>2 \<Turnstile> F \<and> \<A>\<^sub>2 \<Turnstile> G" 
      by (simp only: formula_semantics.simps(4))
    then have C1:"\<A>\<^sub>2 \<Turnstile> F" 
      by (rule conjunct1)
    have F2:"\<A>\<^sub>1 \<Turnstile> F" using H1 C1
      by (rule iffD2)
    have C2:"\<A>\<^sub>2 \<Turnstile> G" using C
      by (rule conjunct2)
    have G2:"\<A>\<^sub>1 \<Turnstile> G" using H2 C2
      by (rule iffD2)
    have "\<A>\<^sub>1 \<Turnstile> F \<and> \<A>\<^sub>1 \<Turnstile> G" using F2 G2
      by (rule conjI)
    thus "\<A>\<^sub>1 \<Turnstile> (F \<^bold>\<and> G)"
      by (simp only: formula_semantics.simps(4))
  qed
qed

lemma relevant_atoms_same_semantics_or: 
  assumes "\<forall>k \<in> atoms F. \<A>\<^sub>1 k = \<A>\<^sub>2 k \<Longrightarrow> \<A>\<^sub>1 \<Turnstile> F \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> F"
          "\<forall>k \<in> atoms G. \<A>\<^sub>1 k = \<A>\<^sub>2 k \<Longrightarrow> \<A>\<^sub>1 \<Turnstile> G \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> G"
          "\<forall>k \<in> atoms (F \<^bold>\<or> G). \<A>\<^sub>1 k = \<A>\<^sub>2 k"
     shows "\<A>\<^sub>1 \<Turnstile> (F \<^bold>\<or> G) \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> (F \<^bold>\<or> G)"
proof -
  have "\<forall>k \<in> atoms F. \<A>\<^sub>1 k = \<A>\<^sub>2 k" using assms(3)
    by simp (* Pendiente *)
  then have H1:"\<A>\<^sub>1 \<Turnstile> F \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> F" 
    by (simp only: assms(1))
  have "\<forall>k \<in> atoms G. \<A>\<^sub>1 k = \<A>\<^sub>2 k" using assms(3)
    by simp (* Pendiente *)
  then have H2:"\<A>\<^sub>1 \<Turnstile> G \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> G" 
    by (simp only: assms(2))
  show "\<A>\<^sub>1 \<Turnstile> (F \<^bold>\<or> G) \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> (F \<^bold>\<or> G)"
  proof (rule iffI)
    assume "\<A>\<^sub>1 \<Turnstile> (F \<^bold>\<or> G)"
    then have C:"\<A>\<^sub>1 \<Turnstile> F \<or> \<A>\<^sub>1 \<Turnstile> G" 
      by (simp only: formula_semantics.simps(5))
    then show "\<A>\<^sub>2 \<Turnstile> (F \<^bold>\<or> G)"
    proof (rule disjE)
      assume D1:"\<A>\<^sub>1 \<Turnstile> F"
      have "\<A>\<^sub>2 \<Turnstile> F" using H1 D1
        by (rule iffD1)
      then have "\<A>\<^sub>2 \<Turnstile> F \<or> \<A>\<^sub>2 \<Turnstile> G"
        by (rule disjI1)
      thus "\<A>\<^sub>2 \<Turnstile> (F \<^bold>\<or> G)" 
        by (simp only: formula_semantics.simps(5))
    next
      assume D2:"\<A>\<^sub>1 \<Turnstile> G"
      have "\<A>\<^sub>2 \<Turnstile> G" using H2 D2
        by (rule iffD1)
      then have "\<A>\<^sub>2 \<Turnstile> F \<or> \<A>\<^sub>2 \<Turnstile> G"
        by (rule disjI2)
      thus "\<A>\<^sub>2 \<Turnstile> (F \<^bold>\<or> G)" 
        by (simp only: formula_semantics.simps(5))
    qed
  next
    assume "\<A>\<^sub>2 \<Turnstile> (F \<^bold>\<or> G)"
    then have C:"\<A>\<^sub>2 \<Turnstile> F \<or> \<A>\<^sub>2 \<Turnstile> G" 
      by (simp only: formula_semantics.simps(5))
    then show "\<A>\<^sub>1 \<Turnstile> (F \<^bold>\<or> G)"
    proof (rule disjE)
      assume D1:"\<A>\<^sub>2 \<Turnstile> F"
      have "\<A>\<^sub>1 \<Turnstile> F" using H1 D1
        by (rule iffD2)
      then have "\<A>\<^sub>1 \<Turnstile> F \<or> \<A>\<^sub>1 \<Turnstile> G"
        by (rule disjI1)
      thus "\<A>\<^sub>1 \<Turnstile> (F \<^bold>\<or> G)" 
        by (simp only: formula_semantics.simps(5))
    next
      assume D2:"\<A>\<^sub>2 \<Turnstile> G"
      have "\<A>\<^sub>1 \<Turnstile> G" using H2 D2
        by (rule iffD2)
      then have "\<A>\<^sub>1 \<Turnstile> F \<or> \<A>\<^sub>1 \<Turnstile> G"
        by (rule disjI2)
      thus "\<A>\<^sub>1 \<Turnstile> (F \<^bold>\<or> G)" 
        by (simp only: formula_semantics.simps(5))
    qed
  qed
qed

lemma relevant_atoms_same_semantics_imp: 
  assumes "\<forall>k \<in> atoms F. \<A>\<^sub>1 k = \<A>\<^sub>2 k \<Longrightarrow> \<A>\<^sub>1 \<Turnstile> F \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> F"
          "\<forall>k \<in> atoms G. \<A>\<^sub>1 k = \<A>\<^sub>2 k \<Longrightarrow> \<A>\<^sub>1 \<Turnstile> G \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> G"
          "\<forall>k \<in> atoms (F \<^bold>\<rightarrow> G). \<A>\<^sub>1 k = \<A>\<^sub>2 k"
     shows "\<A>\<^sub>1 \<Turnstile> (F \<^bold>\<rightarrow> G) \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> (F \<^bold>\<rightarrow> G)"
proof -
  have "\<forall>k \<in> atoms F. \<A>\<^sub>1 k = \<A>\<^sub>2 k" using assms(3)
    by simp (* Pendiente *)
  then have H1:"\<A>\<^sub>1 \<Turnstile> F \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> F" 
    by (simp only: assms(1))
  have "\<forall>k \<in> atoms G. \<A>\<^sub>1 k = \<A>\<^sub>2 k" using assms(3)
    by simp (* Pendiente *)
  then have H2:"\<A>\<^sub>1 \<Turnstile> G \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> G" 
    by (simp only: assms(2))
  show "\<A>\<^sub>1 \<Turnstile> (F \<^bold>\<rightarrow> G) \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> (F \<^bold>\<rightarrow> G)"
  proof (rule iffI)
    assume "\<A>\<^sub>1 \<Turnstile> (F \<^bold>\<rightarrow> G)"
    then have I1:"\<A>\<^sub>1 \<Turnstile> F \<longrightarrow> \<A>\<^sub>1 \<Turnstile> G"
      by (simp only: formula_semantics.simps(6))
    have "\<A>\<^sub>2 \<Turnstile> F \<longrightarrow> \<A>\<^sub>2 \<Turnstile> G"
    proof (rule impI)
      assume F2:"\<A>\<^sub>2 \<Turnstile> F"
      have F1:"\<A>\<^sub>1 \<Turnstile> F" using H1 F2
        by (rule iffD2)
      have G1:"\<A>\<^sub>1 \<Turnstile> G" using I1 F1
        by (rule impE)
      show "\<A>\<^sub>2 \<Turnstile> G" using H2 G1
        by (rule iffD1)
    qed
    thus "\<A>\<^sub>2 \<Turnstile> (F \<^bold>\<rightarrow> G)"
      by (simp only: formula_semantics.simps(6))
  next
    assume "\<A>\<^sub>2 \<Turnstile> (F \<^bold>\<rightarrow> G)"
    then have I2:"\<A>\<^sub>2 \<Turnstile> F \<longrightarrow> \<A>\<^sub>2 \<Turnstile> G"
      by (simp only: formula_semantics.simps(6))
    have "\<A>\<^sub>1 \<Turnstile> F \<longrightarrow> \<A>\<^sub>1 \<Turnstile> G"
    proof (rule impI)
      assume F1:"\<A>\<^sub>1 \<Turnstile> F"
      have F2:"\<A>\<^sub>2 \<Turnstile> F" using H1 F1
        by (rule iffD1)
      have G2:"\<A>\<^sub>2 \<Turnstile> G" using I2 F2
        by (rule impE)
      show "\<A>\<^sub>1 \<Turnstile> G" using H2 G2
        by (rule iffD2)
    qed
    thus "\<A>\<^sub>1 \<Turnstile> (F \<^bold>\<rightarrow> G)"
      by (simp only: formula_semantics.simps(6))
  qed
qed

lemma relevant_atoms_same_semantics_detallada: 
   "\<forall>k \<in> atoms F. \<A>\<^sub>1 k = \<A>\<^sub>2 k \<Longrightarrow> \<A>\<^sub>1 \<Turnstile> F \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> F"
proof (induction F)
case (Atom x)
  then show ?case by (rule relevant_atoms_same_semantics_atomica)
next
  case Bot
then show ?case by (rule relevant_atoms_same_semantics_bot)
next
  case (Not F)
then show ?case by (rule relevant_atoms_same_semantics_not)
next
  case (And F1 F2)
  then show ?case by (rule relevant_atoms_same_semantics_and)
next
case (Or F1 F2)
  then show ?case by (rule relevant_atoms_same_semantics_or)
next
  case (Imp F1 F2)
  then show ?case by (rule relevant_atoms_same_semantics_imp)
qed

lemma relevant_atoms_same_semantics: 
   "\<forall>k \<in> atoms F. \<A>\<^sub>1 k = \<A>\<^sub>2 k \<Longrightarrow> \<A>\<^sub>1 \<Turnstile> F \<longleftrightarrow> \<A>\<^sub>2 \<Turnstile> F"
  by (induction F) simp_all
 
text \<open>Definición: consecuencia lógica.\<close>

definition entailment :: 
  "'a formula set \<Rightarrow> 'a formula \<Rightarrow> bool" ("(_ \<TTurnstile>/ _)" 
    (* \TTurnstile *) [53,53] 53) where
  "\<Gamma> \<TTurnstile> F \<equiv> (\<forall>\<A>. ((\<forall>G \<in> \<Gamma>. \<A> \<Turnstile> G) \<longrightarrow> (\<A> \<Turnstile> F)))"
 
text \<open>We write entailment differently than semantics (\<open>\<Turnstile>\<close> vs. \<open>\<TTurnstile>\<close>).
  For humans, it is usually pretty clear what is meant in a specific
  situation, but it often needs to be decided from context that
  Isabelle/HOL does not have.\<close> 
   
text \<open>Some helpers for the derived connectives\<close>

text \<open>Lemas: enunciar y demostrar detalladamente.\<close>

lemma "A \<Turnstile> \<top>" 
proof -
 have "A \<Turnstile> \<bottom> \<longrightarrow> A \<Turnstile> \<bottom>" 
   by (rule imp_refl)
 then have "A \<Turnstile> (\<bottom> \<^bold>\<rightarrow> \<bottom>)"
   by (simp only: formula_semantics.simps(6))
 thus "A \<Turnstile> \<top>" unfolding Top_def by this
qed
  
lemma top_semantics: 
  "A \<Turnstile> \<top>" 
  unfolding Top_def 
  by simp

lemma BigAnd_semantics: 
  "A \<Turnstile> \<^bold>\<And>F \<longleftrightarrow> (\<forall>f \<in> set F. A \<Turnstile> f)"
  by (induction F; simp)

lemma BigOr_semantics: 
  "A \<Turnstile> \<^bold>\<Or>F \<longleftrightarrow> (\<exists>f \<in> set F. A \<Turnstile> f)" 
  by (induction F; simp)
    
text \<open>Definitions for sets of formulae, used for compactness and model 
  existence.\<close>

text\<open> Definición: conjunto de fórmulas consistente.\<close>

definition "sat S \<equiv> \<exists>\<A>. \<forall>F \<in> S. \<A> \<Turnstile> F"

text \<open>Definición: conjunto de fórmulas finitamente consistente.\<close>

definition "fin_sat S \<equiv> (\<forall>s \<subseteq> S. finite s \<longrightarrow> sat s)"

text \<open>Lema: un conjunto de fórmulas S es inconsistente si y sólo si
 $\bot$ es consecuencia lógica de S.\<close>

lemma "\<Gamma> \<TTurnstile> \<bottom> \<longleftrightarrow> \<not> sat \<Gamma>" 
proof (rule iffI)
  assume "\<Gamma> \<TTurnstile> \<bottom>"
  then have 1:"\<forall>\<A>. ((\<forall>G \<in> \<Gamma>. \<A> \<Turnstile> G) \<longrightarrow> (\<A> \<Turnstile> \<bottom>))"
    by (simp only: entailment_def)
  show "\<not> sat \<Gamma>" 
  proof (rule ccontr)
    assume "\<not> \<not> sat \<Gamma>" 
    then have "sat \<Gamma>" 
      by (rule notnotD)
    then have 2:"\<exists>\<A>. \<forall>F \<in> \<Gamma>. \<A> \<Turnstile> F"
      by (simp only: sat_def)
    obtain "\<B>" where 3:"\<forall>F \<in> \<Gamma>. \<B> \<Turnstile> F" using 2
      by (rule exE)
    have "(\<forall>F \<in> \<Gamma>. \<B> \<Turnstile> F) \<longrightarrow> (\<B> \<Turnstile> \<bottom>)" using 1
      by (rule allE)
    then have "\<B> \<Turnstile> \<bottom>" using 3
      by (rule impE)
    thus "False" 
      by (simp only: formula_semantics.simps(2))
  qed
next
  assume H1:"\<not> sat \<Gamma>" 
  have "\<forall>\<A>. ((\<forall>G \<in> \<Gamma>. \<A> \<Turnstile> G) \<longrightarrow> (\<A> \<Turnstile> \<bottom>))"
  proof (rule allI)
    fix \<A>
    show "(\<forall>G \<in> \<Gamma>. \<A> \<Turnstile> G) \<longrightarrow> (\<A> \<Turnstile> \<bottom>)"
    proof (rule impI)
      assume "\<forall>G \<in> \<Gamma>. \<A> \<Turnstile> G"
      then have "\<exists>\<A>. \<forall>G \<in> \<Gamma>. \<A> \<Turnstile> G"
        by auto (*(rule exI)*)
      then have H2:"sat \<Gamma>"
        by (simp only: sat_def)
      show "\<A> \<Turnstile> \<bottom>" using H1 H2
        by (rule notE)
    qed
  qed
  then show "\<Gamma> \<TTurnstile> \<bottom>"
    by (simp only: entailment_def)
qed

lemma entail_sat: 
  "\<Gamma> \<TTurnstile> \<bottom> \<longleftrightarrow> \<not> sat \<Gamma>" 
  unfolding sat_def entailment_def 
  by simp

(*<*)
end
(*>*) 
