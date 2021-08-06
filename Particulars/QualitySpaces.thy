text_raw \<open>\section[Quality Spaces and Qualia ]{Quality Spaces and Qualia \isalabel{sec:quality-spaces}}\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
In the \autoref{sec:inherence}, the concept of a \emph{moment}
was introduced as a particularization of a property: a moment 
represents a particular property of a particular object. 

In this section, we explain the notion of \emph{quality spaces} and of 
\emph{quality moments} and how they are used as an element for characterizing
properties. The theory presented in this section is a simplification of the
original presentation made in \cite{UFO}, achieved by omitting the concepts of
 complex qualities and complex quality spaces.

The elements introduced so far in the theory enable us to represent substantials, 
moments and the inherence relationship that relate them. These
elements allow us to represent the fact that a substantial has some properties 
and to infer that the particularized properties of a substantial are distinct
from those of another substantial.

However, we they are not enough to determine, for each moment \<open>m\<close>, (1) what 
type of property does \<open>m\<close> represent, e.g. color, height, mood and (2) what
degree, magnitude or value of that type of property that \<open>m\<close> represents.

The notions introduced in this section, \emph{Quality Spaces}, \emph{Qualia},
and the \emph{quale association relation}, enable the representation of these
details.

\<close>

theory \<^marker>\<open>tag aponly\<close> QualitySpaces
  imports "../Misc/Common"
begin \<^marker>\<open>tag aponly\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  A Quality Space is a set whose elements are called \emph{qualia}, in the plural,
  or \emph{quale}, in the singular. We represent the type of qualia elements through
  the type variable \<open>'q\<close>:
\<close>
text_raw \<open>\par\<close>
type_synonym 'q quality_space = \<open>'q set\<close>

locale \<^marker>\<open>tag aponly\<close> quality_space_sig =
  fixes \<Q>\<S> :: \<open>'q quality_space set\<close> and Typ\<^sub>q :: \<open>'q itself\<close>

locale \<^marker>\<open>tag aponly\<close> quality_space = quality_space_sig +
  assumes
    no_empty_quality_space: \<open>\<emptyset> \<notin> \<Q>\<S>\<close> and
    quality_spaces_are_disjoint: 
      \<open>\<lbrakk> Q\<^sub>1 \<in> \<Q>\<S> ; Q\<^sub>2 \<in> \<Q>\<S> ; Q\<^sub>1 \<inter> Q\<^sub>2 \<noteq> \<emptyset> \<rbrakk> \<Longrightarrow> Q\<^sub>1 = Q\<^sub>2\<close>

context quality_space
begin \<^marker>\<open>tag aponly\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  Given a family of sets @{term_type \<open>\<Q>\<S>\<close>}, we call \<open>\<Q>\<S>\<close> a \emph{family of quality spaces}
  just in case the following axioms are valid with respect to \<open>\<Q>\<S>\<close>:
\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
\begin{axiom}[$@{thm_name no_empty_quality_space}$]
   There are no empty sets in \<open>\<Q>\<S>\<close>, i.e., all quality spaces are non-empty:

  \[ @{thm no_empty_quality_space} \]

\end{axiom}

\begin{axiom}[$@{thm_name quality_spaces_are_disjoint}$]
   Quality spaces of \<open>\<Q>\<S>\<close> are disjoint. In other words, any quale is a member of a
   single quality space in \<open>\<Q>\<S>\<close>:

  \[ @{thm quality_spaces_are_disjoint} \]

\end{axiom}
\<close>
text_raw \<open>\par\<close>
end  \<^marker>\<open>tag aponly\<close>

context \<^marker>\<open>tag aponly\<close> quality_space_sig
begin \<^marker>\<open>tag aponly\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>We denote by \<open>\<Q>\<close> the set of all qualia, defined as:\<close>
text_raw \<open>\par\<close>
definition qualia (\<open>\<Q>\<close>) where \<open>\<Q> \<equiv> \<Union> \<Q>\<S>\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  The \<open>qspace\<close> function associates an element of type \<open>'q\<close> to a quality space,
  if is a quale, or to the empty set, if it is not:\<close>
text_raw \<open>\par\<close>
definition qspace :: \<open>'q \<Rightarrow> 'q set\<close> where
  \<open>qspace q \<equiv> if q \<in> \<Q> then THE Q. Q \<in> \<Q>\<S> \<and> q \<in> Q else \<emptyset>\<close>

end  \<^marker>\<open>tag aponly\<close>

context \<^marker>\<open>tag aponly\<close> quality_space_sig
begin \<^marker>\<open>tag aponly\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> \<Q>_I[intro]: 
  assumes \<open>Q \<in> \<Q>\<S>\<close> \<open>q \<in> Q\<close>
  shows \<open>q \<in> \<Q>\<close>
  using assms qualia_def by auto

lemma \<^marker>\<open>tag (proof) aponly\<close>  \<Q>_E[elim]: 
  assumes \<open>q \<in> \<Q>\<close>
  obtains Q where \<open>Q \<in> \<Q>\<S>\<close> \<open>q \<in> Q\<close>
  using assms qualia_def by auto  

lemma  \<^marker>\<open>tag (proof) aponly\<close>  qspace_eq_I1:
  assumes \<open>\<exists>!Q. Q \<in> \<Q>\<S> \<and> q \<in> Q\<close> \<open>q \<in> Q\<close> \<open>Q \<in> \<Q>\<S>\<close>
  shows \<open>qspace q = Q\<close>
proof -
  have A: \<open>q \<in> \<Q>\<close> using assms(2,3) by blast
  show \<open>?thesis\<close> 
    by (auto simp: qspace_def assms A intro!: the1_equality assms)
qed

lemma  \<^marker>\<open>tag (proof) aponly\<close>  qspace_E1:
  assumes \<open>\<exists>!Q. Q \<in> \<Q>\<S> \<and> q \<in> Q\<close> \<open>q \<in> \<Q>\<close>
  obtains \<open>qspace q \<in> \<Q>\<S>\<close> \<open>q \<in> qspace q\<close> 
proof -
  have A: \<open>(THE Q. Q \<in> \<Q>\<S> \<and> q \<in> Q) = qspace q\<close> 
    using qspace_def assms by simp
  let \<open>?P\<close> = \<open>\<lambda>Q. Q \<in> \<Q>\<S> \<and> q \<in> Q\<close>
  show \<open>?thesis\<close> by (metis assms(1) qspace_eq_I1 that)
qed

end \<^marker>\<open>tag (proof) aponly\<close> 

context  \<^marker>\<open>tag (proof) aponly\<close>  quality_space
begin  \<^marker>\<open>tag (proof) aponly\<close> 

lemmas  \<^marker>\<open>tag (proof) aponly\<close> just_quality_space_axioms =
    no_empty_quality_space quality_spaces_are_disjoint

lemmas  \<^marker>\<open>tag (proof) aponly\<close> all_quality_space_axioms =  just_quality_space_axioms

lemma  \<^marker>\<open>tag (proof) aponly\<close> qspace_ex1:
  assumes \<open>q \<in> \<Q>\<close>
  shows \<open>\<exists>!Q. Q \<in> \<Q>\<S> \<and> q \<in> Q\<close>
proof -
  obtain Q where A: \<open>Q \<in> \<Q>\<S>\<close> \<open>q \<in> Q\<close> using assms by blast
  show \<open>?thesis\<close>
  proof (intro ex1I[of _ \<open>Q\<close>] conjI A)
    fix Q'
    assume as: \<open>Q' \<in> \<Q>\<S> \<and> q \<in> Q'\<close>
    then obtain \<open>Q' \<in> \<Q>\<S>\<close> \<open>Q \<inter> Q' \<noteq> \<emptyset>\<close> using A by blast    
    then show \<open>Q' = Q\<close> using quality_spaces_are_disjoint A by metis
  qed
qed

lemma \<^marker>\<open>tag (proof) aponly\<close> qspace_eq_I[intro!]: 
 assumes \<open>q \<in> Q\<close> \<open>Q \<in> \<Q>\<S>\<close>
 shows \<open>qspace q = Q\<close>
  using assms qspace_eq_I1[OF qspace_ex1] by blast

lemma  \<^marker>\<open>tag (proof) aponly\<close> qspace_E[elim]: 
 assumes \<open>q \<in> \<Q>\<close>
 obtains \<open>qspace q \<in> \<Q>\<S>\<close> \<open>q \<in> qspace q\<close>
  using assms qspace_E1[OF qspace_ex1] by blast

lemma  \<^marker>\<open>tag (proof) aponly\<close> qsOf_not_in_Q_empty_iff[iff]: 
    \<open>qspace q = \<emptyset> \<longleftrightarrow> q \<notin> \<Q>\<close>
  by (cases \<open>q \<in> \<Q>\<close> ; (blast | simp add: qspace_def))

lemma \<^marker>\<open>tag (proof) aponly\<close> non_empty_quality_space_1: 
  assumes \<open>Q \<in> \<Q>\<S>\<close>
  obtains q where \<open>q \<in> Q\<close>
  using no_empty_quality_space assms by fastforce

end  \<^marker>\<open>tag (proof) aponly\<close> 

end  \<^marker>\<open>tag (proof) aponly\<close> 