text_raw \<open>\section[Towardness Relation ]{Towardness Relation \isalabel{sec:towardness}}\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
In the UFO theory of endurants, substantials are the bearers of properties. As was explained 
in Section {sec:qualified-particulars}, the intrinsic properties of a substantial are
grounded in the existence of moments which inhere in it and which are associated with
elements from a space of qualia.

Similarly, \emph{material relational properties} are also grounded in the existence of certain
moments. More specifically, there are two kinds of moments that are present whenever a 
material relation exists between two or more substantials: \emph{externally dependent moments},
  whose existence depends not only on its bearer, but also on another substantial, distinct 
from its bearer; and \todo{João P. questions whether or not this definition is outdated: I should emphasize that the definition for relators presented here is from the original work and not from later works.}\emph{relators}, which are complex moments formed by the mereological
sum of externally dependent moments that share a common \emph{founding event}.

In the present work, for the sake of simplifying the theoretical treatment of the 
notion of identity, an effort was made to avoid the introduction of a primitive
parthood relation. However, as explained in the previous paragraph, the notion of
parthood is required for introducing the UFO's notion of a \emph{relator}. 

The adopted alternative was to simplify the characterization of relational reality in 
a way that avoids using parthood relations while, at the same time, preserving a 
minimally useful capability of representing relational reality. To achieve that,
we introduce the relation of \emph{towardness} between a moment and a substantial
distinct from its bearer.

Given a moment \<open>m\<close> inherent to a substantial \<open>s\<close> and another substantial \<open>s\<^sup>*\<close>, distinct
from \<open>s\<close>, if the towardness relation holds between \<open>m\<close> and \<open>s\<^sup>*\<close> then:

\begin{itemize}
\item \<open>m\<close> represents a relational property of \<open>s\<close>;
\item this relational property holds between \<open>s\<close> and \<open>s\<^sup>*\<close>;
\item \<open>m\<close> represents the relational property in the direction \<open>s \<rightarrow> s\<^sup>*\<close>.
\end{itemize}

Such moments are called \emph{directed moments}, since they are, in a sense,
\emph{pointed towards} another substantial then their own bearers.

The fact that \<open>m\<close> represents the particularization of a specific relation
between \<open>s\<close> and \<open>s\<^sup>*\<close> implies that \<open>m\<close> is existentially dependent upon both,
i.e. that \<open>m\<close> is an externally dependent moment. 

Given some substantials \<open>s\<close> and \<open>s\<^sup>*\<close>, some examples of what a moment \<open>m\<close> that
inheres in \<open>s\<close> and is directed to, or stands in a \emph{towardness} relation
with \<open>s\<^sup>*\<close> could represent are:

\begin{itemize}
\item \<open>s\<close> being spatially apart from \<open>s\<^sup>*\<close>;
\item \<open>s\<close> being at specific distance (e.g. 10 km) from \<open>s\<^sup>*\<close>;
\item supposing \<open>s\<close> and \<open>s\<^sup>*\<close> are human beings, \<open>s\<close> being interested in \<open>s\<^sup>*\<close>;
\item \<open>s\<close> being the father of \<open>s\<^sup>*\<close>;
\end{itemize}

At first glance, the notion of directed moments seems very similar to the notion
of externally dependent moments used in the original theory. However, the 
directionality of externally dependent moments, in the original theory, 
is not represented directly, but can be recovered by the existential dependencies
of the moment. However, the towardness relation may be stronger than external existential
dependency, because a moment directed towards a certain substantial will be existentially
dependent also on any other substantials its target is dependent upon.

By representing this directionality explicitly, we give it a status similar 
to what the inherence relation represents. In the same way, for example, that
a representation of a particularized property should contain the explicit representation
of the link between this property and the bearer of the property, i.e. the inherence relation,
the representation of a relational property should also contain the explicit
representation for the link between the property and the target of the relation it
represents.

\todo{João P. questions why ``towards'' is to a single substantial. It is so because we
 chose, for simplicity reasons, to represent only binary material relations between substantials (rels. between moments are excluded).}For the reasons explained before, we do not introduce the notion of a relator as a 
fusion of externally dependent moments or, in this case, of directed moments. Due
to this decision we lose the ability to represent material relations that involve
more than two relata, or that are composed by multiple individual relational 
properties, as an individual. 
\<close>
theory Towardness imports Inherence
begin

subsection \<open>Towardness theory\<close>

locale towardness_sig =
    inherence_sig where Typ\<^sub>p = \<open>Typ\<^sub>p\<close> 
  for 
    towards :: \<open>'p \<Rightarrow> 'p \<Rightarrow> bool\<close> (infix \<open>\<longlongrightarrow>\<close> 75) and
    Typ\<^sub>p :: \<open>'p itself\<close>
begin 

text \<^marker>\<open>tag bodyonly\<close> \<open>Formally, we presume the existence of a relation called
  \<open>towards\<close> that holds between particulars, where we use the
  notation \<open>x \<longlongrightarrow> y\<close> to state that the relation holds between
  particulars \<open>x\<close> and \<open>y\<close>, or that \<open>x\<close> is \emph{directed towards}
  \<open>y\<close>. The towardness relation satisfies the following axioms:\<close>
text_raw\<open>\par\<close>
end \<^marker>\<open>tag aponly\<close>

locale \<^marker>\<open>tag aponly\<close> towardness =
    towardness_sig where Typ\<^sub>p = \<open>Typ\<^sub>p\<close> + inherence where Typ\<^sub>p = \<open>Typ\<^sub>p\<close> 
  for Typ\<^sub>p :: \<open>'p itself\<close> +
  assumes
   towardness_scope: \<open>x \<longlongrightarrow> y \<Longrightarrow> x \<in> \<M> \<and> y \<in> \<S>\<close> and
   towardness_imp_ed[dest]: \<open>x \<longlongrightarrow> y \<Longrightarrow> ed x y\<close> and
   towardness_diff_ultimate_bearers[dest]: \<open>x \<longlongrightarrow> y \<Longrightarrow> !\<beta> x \<noteq> y\<close> and
   towardness_single: \<open>\<lbrakk> x \<longlongrightarrow> y\<^sub>1 ; x \<longlongrightarrow> y\<^sub>2 \<rbrakk> \<Longrightarrow> y\<^sub>1 = y\<^sub>2\<close>
begin

text \<^marker>\<open>tag bodyonly\<close> \<open>
\begin{axiom}[$@{thm_name towardness_scope}$]
  The towardness relation holds between moments and substantials:
  \[ @{thm towardness_scope} \]  
\end{axiom}

\begin{axiom}[$@{thm_name towardness_imp_ed}$]
  A moment being directed towards a substantial implies that the
  former is existentially dependent upon the later:
  \[ @{thm towardness_imp_ed} \]
\end{axiom}

\begin{axiom}[$@{thm_name towardness_diff_ultimate_bearers}$]
  The substantial a directed moment is directed towards must be
  distinct from the substantial that is its ultimate bearer:
  \[ @{thm towardness_diff_ultimate_bearers} \]
\end{axiom}

\begin{axiom}[$@{thm_name towardness_single}$]
  Towardness is unique, i.e. a moment can only be directed towards
  a single substantial:
  \[ @{thm towardness_single} \]
\end{axiom}
\<close>
text_raw\<open>\par\<close>
end \<^marker>\<open>tag aponly\<close>

context \<^marker>\<open>tag aponly\<close> towardness_sig
begin \<^marker>\<open>tag aponly\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>We use the notation \<open>\<M>\<^sub>\<rightarrow>\<close> to represent the set
of directed moments:\<close>
text_raw\<open>\par\<close>
definition directed_moments (\<open>\<M>\<^sub>\<rightarrow>\<close>) where
  \<open>\<M>\<^sub>\<rightarrow> \<equiv> { m . \<exists>x. m \<longlongrightarrow> x }\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> directed_moments_I[intro]: \<open>m \<longlongrightarrow> x \<Longrightarrow> m \<in> \<M>\<^sub>\<rightarrow>\<close> 
  by (auto simp: directed_moments_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> directed_moments_E[elim]: 
  assumes \<open>m \<in> \<M>\<^sub>\<rightarrow>\<close>
  obtains x where \<open>m \<longlongrightarrow> x\<close>
  using assms by (auto simp: directed_moments_def)

end \<^marker>\<open>tag aponly\<close>

context \<^marker>\<open>tag aponly\<close> towardness
begin \<^marker>\<open>tag aponly\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> towardness_unique[intro!]: \<open>Uniq ((\<longlongrightarrow>) x)\<close>
  using towardness_single by (auto simp: Uniq_def)

lemma \<^marker>\<open>tag (proof) aponly\<close> towardness_scopeE[elim]:
  assumes \<open>x \<longlongrightarrow> y\<close>
  obtains \<open>x \<in> \<M>\<close> \<open>y \<in> \<P>\<close> \<open>x \<in> \<P>\<close> \<open>y \<in> \<S>\<close> 
  using assms towardness_scope by auto

lemma \<^marker>\<open>tag (proof) aponly\<close> towardness_scopeD:
  assumes \<open>x \<longlongrightarrow> y\<close>
  shows \<open>x \<in> \<M>\<close> \<open>x \<in> \<P>\<close> \<open>y \<in> \<P>\<close>  \<open>y \<in> \<S>\<close> 
  using assms by auto

lemma \<^marker>\<open>tag (proof) aponly\<close> towardness_apply_to_moments: \<open>x \<longlongrightarrow> y \<Longrightarrow> x \<in> \<M>\<close> 
  using towardness_scope by simp

lemmas \<^marker>\<open>tag aponly\<close> all_towardness_axioms =
    all_inherence_axioms towardness_apply_to_moments towardness_imp_ed    

lemma \<^marker>\<open>tag (proof) aponly\<close> directed_moments_are_moments: \<open>\<M>\<^sub>\<rightarrow> \<subseteq> \<M>\<close>
  using towardness_scope directed_moments_E
  by blast  

end \<^marker>\<open>tag aponly\<close>

end \<^marker>\<open>tag aponly\<close>