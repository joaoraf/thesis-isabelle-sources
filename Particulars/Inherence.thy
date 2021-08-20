text_raw \<open>\section[Substantials, Moments and Inherence ]{Substantials, Moments and Inherence \isalabel{sec:inherence}}\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  In this section, we present a theory about UFO's \emph{inherence} relation and the two categories
  of UFO endurants that are distinguished through it: \emph{Substantials} and \emph{Moments}.
  We present several candidate theories for the inherence relation, beginning with one that
  is based on the axioms from the UFO's original work \cite{UFO}. We identify some undesirable 
  properties, or anomalies, that are derivable from the original axiomatization and, for each 
  anomaly, we propose additional axioms that exclude it. Afterwards, we prove that those 
  additional axioms and a few of the original ones are logically
  equivalent to the requirement that the inherence relation must be a \gls{noetherian-relation}. 
  We end this section by proposing the theory of inherence which shall be used in this thesis.
\<close>
text_raw\<open>\par\<close>
theory \<^marker>\<open>tag aponly\<close> Inherence
  imports  PossibleWorlds
begin \<^marker>\<open>tag aponly\<close>

no_notation \<^marker>\<open>tag aponly\<close> nth (infixl \<open>!\<close> 100) 

locale inherence_sig = possible_worlds_sig where Typ\<^sub>p = \<open>Typ\<^sub>p\<close> 
  for
     Typ\<^sub>p :: \<open>'p itself\<close> +
  fixes
    inheresIn :: \<open>'p \<Rightarrow> 'p \<Rightarrow> bool\<close> (infix \<open>\<triangleleft>\<close> 75)
begin 

text \<^marker>\<open>tag bodyonly\<close> \<open>
  The basic signature of the inherence relation theories presented in this section extends
  the signature of the @{locale possible_worlds} theory with a single symbol that 
  denotes the inherence relation:\<close>

text_raw \<^marker>\<open>tag bodyonly\<close> \<open>
\begin{tabular}{ll>{\raggedright}p{5cm}}
Symbol & Type & Denotation \tabularnewline
\hline
$@{term "(\<triangleleft>)"}$  & $@{typeof \<open>(\<triangleleft>)\<close>}$ & inherence relation (\<open>inheresIn\<close>), where @{term \<open>x \<triangleleft> y\<close>} denotes 
                                                  that \<open>x\<close> \emph{inheres in} \<open>y\<close>
\end{tabular}
\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
The inherence relation is the link between an endurant and its particularized properties. 
For example, when we say that "John's eye is blue", it is represented here as the existence
of two endurants, "John's eye" and "John's eye being blue", where the later, a particularized
property, is said to "inhere" in the former. Conversely, the former is said to "bear" the later,
or to be the later's \emph{bearer}.

In other words, any endurant may \emph{bear} particularized properties that characterize it,
being themselves also endurants. Those endurants that represent particularized properties are
called \emph{moments}, while those that do not are called \emph{substantials}. \<close>
text_raw\<open>\par\<close>
end

locale \<^marker>\<open>tag aponly\<close> inherence_base =
    possible_worlds where Typ\<^sub>p = \<open>Typ\<^sub>p\<close>  +
    inherence_sig where Typ\<^sub>p = \<open>Typ\<^sub>p\<close> 
  for
     Typ\<^sub>p :: \<open>'p itself\<close> +
  assumes    
    \<comment> \<open>Axiom (3) on page 213\<close>
    inherence_scope: \<open>x \<triangleleft> y \<Longrightarrow> x \<in> \<E> \<and> y \<in> \<E>\<close> and
    \<comment> \<open>Axiom (4) on page 213\<close>
    inherence_imp_ed: \<open>x \<triangleleft> y \<Longrightarrow> ed x y\<close> and    
    \<comment> \<open>Axiom (9) on page 214\<close>
    moment_non_migration: \<open>\<lbrakk> x \<triangleleft> y ; x \<triangleleft> z \<rbrakk> \<Longrightarrow> y = z\<close>
begin \<^marker>\<open>tag aponly\<close>

lemmas \<^marker>\<open>tag aponly\<close> just_inherence_base_axioms =    
  inherence_scope inherence_imp_ed
lemmas \<^marker>\<open>tag aponly\<close> all_inherence_base_axioms =
  all_possible_worlds_axioms
  just_inherence_base_axioms

text \<^marker>\<open>tag bodyonly\<close> \<open>
The inherence relation is restricted by the following axioms that, when added to the 
@{locale possible_worlds} theory, form what we call the @{locale inherence_base} theory,
 a minimal set of axioms for all the inherence theories presented in this section:

  \begin{axiom}[$@{thm_name inherence_scope}$\ufoformulafootnote{213}{3}]
    The inherence relation is restricted to \emph{endurants} only:

    \[ @{thm inherence_scope} \]  
  \end{axiom}

  \begin{axiom}[$@{thm_name inherence_imp_ed}$\ufoformulafootnote{213}{4}]
    The existence of a moment must, of course, imply the existence of its bearer:

    \[ @{thm inherence_imp_ed} \]
  \end{axiom}

  \begin{axiom}[$@{thm_name moment_non_migration}$\ufoformulafootnote{214}{9}]
    Moments inhere in a single bearer:
  
    \[ @{thm moment_non_migration} \]
  \end{axiom}
\<close>
text_raw\<open>\par\<close>
end \<^marker>\<open>tag aponly\<close>

context \<^marker>\<open>tag aponly\<close> inherence_sig
begin \<^marker>\<open>tag aponly\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  Using the inherence relation we can define the sets of
  moments and substantials, that are represented, respectively, by the symbols 
  \<open>\<M>\<close>\ufoformulafootnote{214}{8} and \<open>\<S>\<close>\ufoformulafootnote{215}{11}:
\<close>
text_raw\<open>\par\<close>
definition \<M> where \<open>\<M> \<equiv> { x . \<exists>y. x \<triangleleft> y }\<close> 

lemma \<^marker>\<open>tag (proof) aponly\<close> \<M>_I[intro]: \<open>x \<triangleleft> y \<Longrightarrow> x \<in> \<M>\<close> 
  using \<M>_def by auto

lemma \<^marker>\<open>tag (proof) aponly\<close> \<M>_E[elim]:
  assumes \<open>x \<in> \<M>\<close>
  obtains y where \<open>x \<triangleleft> y\<close> 
  using assms \<M>_def by auto

definition \<S> where \<open>\<S> \<equiv> \<E> - \<M>\<close> 

lemma \<^marker>\<open>tag (proof) aponly\<close> \<S>_I[intro!]: 
  assumes \<open>x \<in> \<E>\<close> \<open>x \<notin> \<M>\<close>
  shows \<open>x \<in> \<S>\<close>
  using assms \<S>_def by auto

lemma \<^marker>\<open>tag (proof) aponly\<close> \<S>_E[elim!]:
  assumes \<open>x \<in> \<S>\<close>
  obtains \<open>x \<in> \<E>\<close> \<open>x \<notin> \<M>\<close>
  using assms \<S>_def by auto

text \<^marker>\<open>tag bodyonly\<close> \<open>
  The \emph{bearer} of a moment, i.e. the endurant it inheres in, is given by the function \<open>\<beta>\<close> 
  (\<open>bearer\<close>), defined as:\<close>

definition bearer :: \<open>'p \<Rightarrow> 'p\<close> (\<open>\<beta>\<close>) where \<open>\<beta> m \<equiv> THE x. m \<triangleleft> x\<close>
  
text \<^marker>\<open>tag bodyonly\<close> \<open>
 Since the transitive closure of the inherence relation shall play a role in
 some proofs, we introduce here a special syntax that denotes it:
\<close>
text_raw\<open>\par\<close>
abbreviation inheres_in_trancl :: \<open>'p \<Rightarrow> 'p \<Rightarrow> bool\<close> (infix \<open>\<triangleleft>\<triangleleft>\<close>  75)
    where \<open>x \<triangleleft>\<triangleleft> y \<equiv> (\<triangleleft>)\<^sup>+\<^sup>+ x y\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  Similarly, we also represent the n-th transitive iteration of the inherence relation using
  a special syntax:
\<close>
text_raw\<open>\par\<close>
abbreviation inheres_in_by 
    :: \<open>'p \<Rightarrow> nat \<Rightarrow> 'p \<Rightarrow> bool\<close> (\<open>_ \<triangleleft>\<triangleleft>\<^bsup>_\<^esup> _\<close> [74,1,74] 75)
  where \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> y \<equiv> ((\<triangleleft>)^^n) x y\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  The n-th transitive iteration is defined for every natural number \<open>n\<close>. In special, the
   0-th iteration is simply the identity relation. Other examples include the 1-th iteration,
  which is simply the inherence relation itself, and the 2-th iteration, \<open>x \<triangleleft>\<triangleleft>\<^bsup>2\<^esup> y\<close>, which is
  equivalent to \<open>\<exists>z. x \<triangleleft> z \<and> z \<triangleleft> y\<close>.   The \emph{n-th bearer} of a moment is defined as the 
  endurant to which is linked by a n-th iteration of the inherence relation:
\<close>
text_raw\<open>\par\<close>
definition nth_bearer :: \<open>'p \<Rightarrow> nat \<Rightarrow> 'p\<close> (\<open>#\<beta>\<close>)
    where \<open>#\<beta> m n \<equiv> THE x. m \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> x\<close>

end \<^marker>\<open>tag aponly\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  In the context of a @{locale inherence_base} theory, the following lemmas hold:
\<close>
text_raw\<open>\par\<close>
context \<^marker>\<open>tag aponly\<close> inherence_base
begin \<^marker>\<open>tag aponly\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>The bearer function is well defined for moments:\<close>
text_raw\<open>\par\<close>
lemma bearer_eqI:
  assumes \<open>x \<triangleleft> y\<close>
  shows \<open>\<beta> x = y\<close>
proof \<^marker>\<open>tag aponly\<close> 
    (simp add: bearer_def ; intro the1_equality assms)
  show \<open>\<exists>!y. x \<triangleleft> y\<close> \<^marker>\<open>tag aponly\<close>
    apply (intro ex1I[of _ y] assms)
    using moment_non_migration assms by metis
qed

text \<^marker>\<open>tag bodyonly\<close> \<open>
  Every moment inhere in the endurant given by the bearer function:
\<close>
text_raw\<open>\par\<close>
lemma bearerI:
  assumes \<open>x \<in> \<M>\<close>
  shows \<open>x \<triangleleft> \<beta> x\<close>
proof \<^marker>\<open>tag aponly\<close> 
  (simp add: bearer_def ; rule the1I2 ; assumption?)
  have \<open>\<exists>y. x \<triangleleft> y\<close> using assms \<M>_def by blast
  then show \<open>\<exists>!y. x \<triangleleft> y\<close>
    apply (intro ex_ex1I, assumption)
    using moment_non_migration assms by metis
qed
  
text \<^marker>\<open>tag bodyonly\<close> \<open>
  Nth-bearers, when they exist, are also unique:
\<close>
text_raw\<open>\par\<close>
lemma nth_inherence_unique_cond:
  assumes \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> y\<close> \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> z\<close> 
  shows \<open>y = z\<close>
proof \<^marker>\<open>tag aponly\<close> (insert assms ; induct n arbitrary: y z rule: less_induct)
  fix i y z
  assume A: \<open>\<And>j y z. \<lbrakk> j < i ; x \<triangleleft>\<triangleleft>\<^bsup>j\<^esup> y ; x \<triangleleft>\<triangleleft>\<^bsup>j\<^esup> z \<rbrakk> \<Longrightarrow> y = z\<close>
         \<open>x \<triangleleft>\<triangleleft>\<^bsup>i\<^esup> y\<close> \<open>x \<triangleleft>\<triangleleft>\<^bsup>i\<^esup> z\<close>
  consider (zero) \<open>i = 0\<close> | (succ) j where \<open>i = Suc j\<close>     
    using not0_implies_Suc by blast
  then show \<open>y = z\<close>
  proof(cases)
    case zero
    then show ?thesis using A(2,3) by auto
  next
    case succ
    then obtain y\<^sub>1 where Y1: \<open>x \<triangleleft>\<triangleleft>\<^bsup>j\<^esup> y\<^sub>1\<close> \<open>y\<^sub>1 \<triangleleft> y\<close> using A(2)
      by auto
    obtain z\<^sub>1 where Z1: \<open>x \<triangleleft>\<triangleleft>\<^bsup>j\<^esup> z\<^sub>1\<close> \<open>z\<^sub>1 \<triangleleft> z\<close> using A(3) succ
      by auto
    have \<open>j < i\<close> using succ by auto
    then have \<open>y\<^sub>1 = z\<^sub>1\<close> 
      using A(1) Y1(1) Z1(1) by metis
    then have \<open>y\<^sub>1 \<triangleleft> z\<close> using Z1(2) by simp    
    then show ?thesis 
      using moment_non_migration Y1(2) by metis
  qed
qed

text \<^marker>\<open>tag bodyonly\<close> \<open>
  Under the same condition, nth-bearers coincide, if they exist,
      with the nth-iteration of the bearer function:\<close>
text_raw\<open>\par\<close>
lemma nth_bearer_eq_nth_iteration_of_bearer: 
  assumes nth_bearer_exists: \<open>\<exists>y. x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> y\<close> 
  shows \<open>#\<beta> x n = (\<beta> ^^ n) x\<close>
proof \<^marker>\<open>tag aponly\<close> (simp add: nth_bearer_def ; intro the1_equality)
  show \<open>\<exists>!y. x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> y\<close>
  proof (intro ex_ex1I nth_bearer_exists)
    fix y z
    assume \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> y\<close> \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> z\<close>
    then show \<open>y = z\<close>
      using nth_inherence_unique_cond 
      by metis 
  qed
next
  show \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> (\<beta> ^^ n) x\<close>
    using nth_bearer_exists apply (induct n ; simp)
    subgoal for n
      apply (intro relcomppI[of _ _ \<open>(\<beta> ^^ n) x\<close>])
      subgoal G1 by blast
      apply (intro bearerI ; simp add: \<M>_def)      
      using moment_non_migration nth_inherence_unique_cond by blast
    done
qed

text \<^marker>\<open>tag bodyonly\<close> \<open>
   There are no separate bearer chains, i.e. if \<open>y\<^sub>1\<close> and \<open>y\<^sub>2\<close> are
 indirect bearers of the same moment \<open>x\<close>, then one of them must be an
 indirect bearer of the other, depending on how many inherence 
 ``steps'' they are from \<open>x\<close>:
\<close>
text_raw\<open>\par\<close>
lemma inherence_mid_point[intro]: 
  \<open>y\<^sub>1 \<triangleleft>\<triangleleft>\<^bsup>(n-m)\<^esup> y\<^sub>2\<close> if assms: \<open>x \<triangleleft>\<triangleleft>\<^bsup>m\<^esup> y\<^sub>1\<close> \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> y\<^sub>2\<close> \<open>m \<le> n\<close>
proof \<^marker>\<open>tag aponly\<close> -
  have \<open>n = m + (n - m)\<close> using \<open>m \<le> n\<close> by presburger
  then have \<open>x \<triangleleft>\<triangleleft>\<^bsup>(m + (n - m))\<^esup> y\<^sub>2\<close> using assms(2) by simp
  then have X: \<open>(((\<triangleleft>)^^m) OO ((\<triangleleft>)^^(n - m))) x y\<^sub>2\<close> 
    using relpowp_add by metis
  obtain z where A: \<open>x \<triangleleft>\<triangleleft>\<^bsup>m\<^esup> z\<close> \<open>z \<triangleleft>\<triangleleft>\<^bsup>(n - m)\<^esup> y\<^sub>2\<close> 
    using X[THEN relcomppE]
    by metis
  then have \<open>z = y\<^sub>1\<close> 
    using nth_inherence_unique_cond assms(1) by metis
  then show \<open>y\<^sub>1 \<triangleleft>\<triangleleft>\<^bsup>(n - m)\<^esup> y\<^sub>2\<close> using A(2) by simp
qed


end \<^marker>\<open>tag aponly\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  From the idea that moment may inhere in other moments, which themselves
  can be other moments, comes the notion of the \emph{order of a moment}:
  a first-order moment is a moment that inheres in a substantial, a 
  second-order moment is a moment that inheres in a first-order moment,
  etc.

  Since a moment has an order of, at minimum, one, we can add substantials
  as a special case, saying that they have order 0.

  Endurants can form chains linked by the inherence relation. For a moment \<open>m\<close>, 
  a substantial that limits its inherence chain, if it exists,
  is called an ultimate bearer of \<open>m\<close>.

  Formally, we define these notions as:
\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  If \<open>x\<close> is a moment, then an endurant \<open>y\<close> is considered an \emph{ultimate bearer} of \<open>x\<close>
  if and only if \<open>x\<close> is either equal to \<open>y\<close> or \<open>x\<close> inheres transitively in \<open>y\<close>, 
  and \<open>y\<close> is a substantial:
\<close>
text_raw\<open>\par\<close>
context \<^marker>\<open>tag aponly\<close> inherence_sig
begin \<^marker>\<open>tag aponly\<close>

definition is_an_ultimate_bearer_of :: \<open>'p \<Rightarrow> 'p \<Rightarrow> bool\<close>
  where \<open>is_an_ultimate_bearer_of x y \<longleftrightarrow> (\<triangleleft>)\<^sup>*\<^sup>* y x \<and> x \<in> \<S>\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  If \<open>x\<close> inheres in \<open>y\<close> by \<open>n\<close> steps, i.e. \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> y\<close>, and \<open>y\<close> is an ultimate bearer of \<open>x\<close>,
  then we say that \<open>x\<close> has order \<open>n\<close>. Otherwise, if \<open>x\<close> is a substantial,
  we say that \<open>x\<close> has order 0:
\<close>
text_raw\<open>\par\<close>
definition has_order :: \<open>'p \<Rightarrow> nat \<Rightarrow> bool\<close> 
  where \<open>has_order x n \<longleftrightarrow>
          (\<exists>y. x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> y \<and> is_an_ultimate_bearer_of y x)\<close>

end \<^marker>\<open>tag aponly\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>In the context of a @{locale inherence_base} theory, we can prove the following lemmas:\<close>
text_raw\<open>\par\<close>
context  \<^marker>\<open>tag aponly\<close> inherence_base
begin  \<^marker>\<open>tag aponly\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> moments_are_endurants: \<open>\<M> \<subseteq> \<E>\<close>
  by (auto simp: \<M>_def inherence_scope)

lemma \<^marker>\<open>tag (proof) aponly\<close> ultimate_bearer_unique:
  assumes 
    \<open>x \<in> \<E>\<close> 
    \<open>is_an_ultimate_bearer_of y x\<close>
    \<open>is_an_ultimate_bearer_of z x\<close>
  shows \<open>y = z\<close>
proof -
  obtain Y: \<open>(\<triangleleft>)\<^sup>*\<^sup>* x y\<close> \<open>\<And>w. \<not> y \<triangleleft> w\<close> \<open>y \<in> \<E>\<close>
    using assms(1,2) is_an_ultimate_bearer_of_def \<S>_def \<M>_def
    by auto
  obtain Z: \<open>(\<triangleleft>)\<^sup>*\<^sup>* x z\<close> \<open>\<And>w. \<not> z \<triangleleft> w\<close> \<open>z \<in> \<E>\<close>
    using assms(1,3) is_an_ultimate_bearer_of_def \<S>_def \<M>_def
    by auto  
  have cases: \<open>y = z \<or> y \<triangleleft>\<triangleleft> z \<or> z \<triangleleft>\<triangleleft> y\<close>
    if A: \<open>x \<triangleleft>\<triangleleft> y\<close> \<open>x \<triangleleft>\<triangleleft> z\<close>
    for x y z
  proof (intro verit_and_pos(4) ; rule ccontr)
    assume B: \<open>y \<noteq> z\<close> \<open>\<not> y \<triangleleft>\<triangleleft> z\<close> \<open>\<not> z \<triangleleft>\<triangleleft> y\<close>
    show False using A(1,2) B 
    proof (induct arbitrary: z rule: tranclp_induct)
      case (base y z)      
      then show ?case
      proof (cases \<open>x \<triangleleft> z\<close>)
        assume \<open>x \<triangleleft> z\<close>
        then have \<open>z = y\<close> 
          using \<open>x \<triangleleft> y\<close> moment_non_migration by auto
        then show False using \<open>y \<noteq> z\<close> by simp
      next
        assume \<open>\<not> x \<triangleleft> z\<close>
        then obtain w where \<open>x \<triangleleft> w\<close> \<open>w \<triangleleft>\<triangleleft> z\<close>
          using \<open>x \<triangleleft>\<triangleleft> z\<close> by (metis rtranclpD tranclpD)
        then have \<open>w = y\<close> 
          using \<open>x \<triangleleft> y\<close> moment_non_migration by auto
        then have \<open>y \<triangleleft>\<triangleleft> z\<close> using \<open>w \<triangleleft>\<triangleleft> z\<close> by simp
        then show False using \<open>\<not> y \<triangleleft>\<triangleleft> z\<close> by simp
      qed
    next
      case (step y\<^sub>1 z\<^sub>1 z\<^sub>2)      
      then show False        
        by (metis moment_non_migration rtranclpD 
                  tranclp.trancl_into_trancl tranclpD)        
    qed
  qed
  obtain \<open>\<not> y \<triangleleft>\<triangleleft> z\<close> \<open>\<not> z \<triangleleft>\<triangleleft> y\<close> 
    using Y(2) Z(2) by (metis tranclpD)
  then show \<open>y = z\<close> 
    using cases Y(1) Z(1) by (metis rtranclpD)
qed

text \<^marker>\<open>tag bodyonly\<close> \<open>
  \begin{lemma}[$@{thm_name ultimate_bearer_unique}$]
  Ultimate bearers, whenever they exist, are unique:

  @{thm[display] ultimate_bearer_unique}

  \end{lemma}
\<close>
text_raw\<open>\par\<close>
lemma \<^marker>\<open>tag (proof) aponly\<close> ultimate_bearer_unique_order:
  assumes \<open>x \<in> \<E>\<close> \<open>is_an_ultimate_bearer_of y x\<close>    
  shows \<open>\<exists>!n. has_order x n\<close>
proof (cases \<open>x \<in> \<M>\<close>)
  assume \<open>x \<notin> \<M>\<close>
  then have \<open>x \<in> \<S>\<close> using \<open>x \<in> \<E>\<close> \<S>_def by simp  
  then have \<open>has_order x 0\<close>
    by (auto simp: has_order_def is_an_ultimate_bearer_of_def)
  have \<open>n = 0\<close> if \<open>has_order x n\<close> for n
    using that 
    apply (auto simp: has_order_def is_an_ultimate_bearer_of_def 
           \<S>_def \<M>_def)
    apply (rule ccontr ; simp)    
    using \<open>x \<notin> \<M>\<close> \<M>_def 
    by (metis mem_Collect_eq tranclp_power tranclpD)
  then show ?thesis     
    using \<open>has_order x 0\<close> by metis
next  
  assume \<open>x \<in> \<M>\<close>
  show ?thesis
  proof -  
    have \<open>x \<in> \<E>\<close> 
      using assms(1) moments_are_endurants by auto
    have R1: \<open>Suc i = j\<close>  if \<open>i = j - 1\<close> \<open>0 < j\<close> for i j 
      using that by auto  
    have R2: \<open>\<delta> = 0\<close> 
      if A: \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> y\<close> \<open>x \<triangleleft>\<triangleleft>\<^bsup>n+\<delta>\<^esup> y\<close> \<open>\<forall>z. \<not> y \<triangleleft> z\<close> for x y n \<delta>
    proof -
      obtain z where \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> z\<close> \<open>z \<triangleleft>\<triangleleft>\<^bsup>\<delta>\<^esup> y\<close> 
        using A(2) by (metis relcomppE relpowp_add)
      then have \<open>z = y\<close> 
        using A(1) nth_inherence_unique_cond moment_non_migration
        by metis
      then have \<open>y \<triangleleft>\<triangleleft>\<^bsup>\<delta>\<^esup> y\<close> using \<open>z \<triangleleft>\<triangleleft>\<^bsup>\<delta>\<^esup> y\<close> by simp
      have False if \<open>0 < \<delta>\<close>
      proof -
        obtain \<gamma> where \<open>\<delta> = Suc \<gamma>\<close>  using \<open>0 < \<delta>\<close> gr0_conv_Suc by blast
        then obtain q where \<open>y \<triangleleft> q\<close> 
          using \<open>y \<triangleleft>\<triangleleft>\<^bsup>\<delta>\<^esup> y\<close> 
          by (meson relpowp_Suc_D2)
        then show False using A(3) by simp
      qed
      then show ?thesis by auto
    qed
    have R3: \<open>n\<^sub>1 = n\<^sub>2\<close> 
      if A: \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^sub>1\<^esup> y\<close> \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^sub>2\<^esup> y\<close> \<open>\<forall>z. \<not> y \<triangleleft> z\<close> for x y n\<^sub>1 n\<^sub>2
    proof -
      consider 
          (C1) \<open>n\<^sub>1 = n\<^sub>2\<close> 
        | (C2) \<delta> where \<open>n\<^sub>2 = n\<^sub>1 + \<delta>\<close> 
        | (C3) \<delta> where \<open>n\<^sub>1 = n\<^sub>2 + \<delta>\<close>      
        by (meson le_Suc_ex linear)
      then show ?thesis
      proof (cases)
        case C1 then show ?thesis by assumption
      next
        case C2 then show ?thesis using A R2 by simp          
      next
        case C3 then show ?thesis using A R2 by simp
      qed
    qed
    obtain R4: \<open>x \<triangleleft>\<triangleleft> y\<close> \<open>y \<in> \<S>\<close> \<open>\<forall>z. \<not> y \<triangleleft> z\<close> \<open>y \<in> \<E>\<close>
      using assms(2) 
      by (metis CollectI Diff_iff \<S>_def \<open>x \<in> \<M>\<close> \<M>_def
                is_an_ultimate_bearer_of_def rtranclpD)
    have R5: \<open>n\<^sub>1 = n\<^sub>2\<close> if \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^sub>1\<^esup> y\<close> \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^sub>2\<^esup> y\<close> for n\<^sub>1 n\<^sub>2
      using that R3 R4(3) by metis
    obtain n where R6: \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> y\<close> 
      using R4(1) by (meson tranclp_power)
    have R7: \<open>n\<^sub>1 = n\<close> if \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^sub>1\<^esup> y\<close> for n\<^sub>1 
      using R5 R6 that by metis
    have R8: \<open>has_order x n\<close> 
      using R6 assms(2) has_order_def by (auto simp: has_order_def)
    obtain \<open>x \<notin> \<S>\<close>  using \<S>_def \<open>x \<in> \<M>\<close> by auto
    then have R9: \<open>n\<^sub>1 = n\<close> 
      if \<open>has_order x n\<^sub>1\<close> for n\<^sub>1 
      using that apply (auto simp: has_order_def)    
      subgoal by (simp add: assms(1))
      subgoal premises P for z
        using P R7 assms(1) assms(2) ultimate_bearer_unique by blast        
      done
    show ?thesis
      using R8 R9 by metis
  qed
qed

text \<^marker>\<open>tag bodyonly\<close> \<open>
  \begin{lemma}[$@{thm_name ultimate_bearer_unique_order}$]

  If an endurant has an ultimate bearer, then it has a
  unique order:
  
  @{thm[display] ultimate_bearer_unique_order [no_vars]} 

  \end{lemma}
\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>  
  It is reasonable to expect, in UFO's conceptualization of inherence, that every moment has a 
  determinate order and a unique ultimate bearer. A moment cannot be simultaneously, a first-order
  moment and a second-order moment. Nor should it have more than one ultimate bearer, since a moment
  represents the particularization of a property of \emph{one} individual. This uniqueness is 
  guaranteed as long as every moment have an ultimate bearer, as shown in lemmas 
  @{thm_name ultimate_bearer_unique} and @{thm_name ultimate_bearer_unique_order}. 
  In order to show that UFO's axiomatization of inherence guarantees the well-definedness of 
  these concepts, it is necessary and sufficient to prove that every moment has an ultimate
  bearer.
\<close>
text_raw\<open>\par\<close>
lemma \<^marker>\<open>tag (proof) aponly\<close> inherence_scopeE[elim]: 
  assumes \<open>x \<triangleleft> y\<close>
  obtains \<open>x \<in> \<M>\<close> \<open>y \<in> \<E>\<close>
  using assms inherence_scope by auto

lemma \<^marker>\<open>tag (proof) aponly\<close> endurantI1[intro]: \<open>x \<in> \<M> \<Longrightarrow> x \<in> \<E>\<close>
  using inherence_scope by blast

lemma \<^marker>\<open>tag (proof) aponly\<close> endurantI2: \<open>x \<triangleleft> y \<Longrightarrow> y \<in> \<E>\<close> by auto

lemma \<^marker>\<open>tag (proof) aponly\<close> endurantI3[intro]: \<open>x \<in> \<S> \<Longrightarrow> x \<in> \<E>\<close> by blast

lemma \<^marker>\<open>tag (proof) aponly\<close> substantials_are_endurants: \<open>\<S> \<subseteq> \<E>\<close> by auto

lemma \<^marker>\<open>tag (proof) aponly\<close> subst_moments_are_disj: \<open>\<S> \<inter> \<M> = \<emptyset>\<close> by auto

lemma \<^marker>\<open>tag (proof) aponly\<close> endurants_eq_un_moments_subst: \<open>\<E> = \<S> \<union> \<M>\<close> by auto

lemma \<^marker>\<open>tag (proof) aponly\<close> endurant_cases[cases set]:
  assumes \<open>x \<in> \<E>\<close>
  obtains (substantial) \<open>x \<in> \<S>\<close> 
        | (moment) \<open>x \<in> \<M>\<close>
  using assms 
  by auto

lemma \<^marker>\<open>tag (proof) aponly\<close> bearer_ex1[intro]: \<open>\<exists>!y. x \<triangleleft> y\<close> if \<open>x \<in> \<M>\<close>
  using moment_non_migration ex_ex1I[of \<open>\<lambda>y. x \<triangleleft> y\<close>] \<open>x \<in> \<M>\<close> 
  by blast

lemma \<^marker>\<open>tag (proof) aponly\<close> inheres_in_bearerI[intro]: \<open>x \<triangleleft> \<beta> x\<close> if \<open>x \<in> \<M>\<close>
  using \<open>x \<in> \<M>\<close> bearer_eqI moment_non_migration 
  by blast

lemma \<^marker>\<open>tag (proof) aponly\<close> inheres_in_by_scope: 
  assumes \<open>0 < n\<close> \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> y\<close>
  obtains \<open>x \<in> \<M>\<close> \<open>y \<in> \<E>\<close>
proof 
  obtain k\<^sub>1 where \<open>x \<triangleleft> k\<^sub>1\<close> 
    using assms by (metis less_not_refl2 relpowp_E2)
  then show \<open>x \<in> \<M>\<close> using that by blast
  obtain k\<^sub>2 where \<open>k\<^sub>2 \<triangleleft> y\<close> 
    using assms by (metis less_not_refl2 relpowp_E)
  then show \<open>y \<in> \<E>\<close> using that by blast
qed

lemma \<^marker>\<open>tag (proof) aponly\<close> trans_inheres_in_scope:
  assumes \<open>x \<triangleleft>\<triangleleft> y\<close>
  obtains \<open>x \<in> \<M>\<close> \<open>y \<in> \<E>\<close>
proof -
  obtain n where \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> y\<close> \<open>0 < n\<close> 
    using assms by (meson tranclp_power)
  then show \<open>?thesis\<close> using that inheres_in_by_scope by metis
qed

lemma \<^marker>\<open>tag (proof) aponly\<close> nth_bearer_eqI[intro!]: 
    \<open>#\<beta> x n = y\<close> if assms: \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> y\<close> for x y n
  apply (simp only: nth_bearer_def)
  using the1_equality nth_inherence_unique_cond assms 
  by metis

lemma \<^marker>\<open>tag (proof) aponly\<close> nth_bearerI[intro!]: 
    \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> (#\<beta> x n)\<close> if assms: \<open>\<exists>y. x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> y\<close> for x n
  apply (simp only: nth_bearer_def)
  using the1I2 assms nth_inherence_unique_cond 
  by (metis (no_types, hide_lams))

lemma \<^marker>\<open>tag (proof) aponly\<close> zeroth_bearer[simp]: \<open>#\<beta> x 0 = x\<close>
  using nth_bearerI by auto

lemma \<^marker>\<open>tag (proof) aponly\<close> nth_bearer_range: 
  \<open>#\<beta> x n \<in> \<E>\<close> if assms: \<open>\<exists>y. x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> y\<close> \<open>0 < n\<close> for x n
proof -
  have \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> (#\<beta> x n)\<close> using assms by blast
  then show \<open>?thesis\<close> 
    using \<open>0 < n\<close> inheres_in_by_scope assms 
    by blast
qed

lemma \<^marker>\<open>tag (proof) aponly\<close> nth_bearer_range': 
    \<open>#\<beta> x n \<in> \<E>\<close> if assms: \<open>\<exists>y. x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> y\<close> \<open>x \<in> \<E>\<close> for x n
  using assms 
  by (cases \<open>n = 0\<close> ; auto intro!: nth_bearer_range)

lemma \<^marker>\<open>tag (proof) aponly\<close> particular_cases_1[cases set]:
  assumes \<open>x \<in> \<P>\<close>
  obtains (substantial) \<open>x \<in> \<S>\<close> 
        | (moment) \<open>x \<in> \<M>\<close>
  using assms by auto  

end \<^marker>\<open>tag aponly\<close>

locale \<^marker>\<open>tag aponly\<close> inherence_original =
  inherence_base +
  assumes
   (* Axiom (5) on page 213 *)
  inherence_irrefl: \<open>\<not> x \<triangleleft> x\<close> and
   (* Axiom (6) on page 213 *)
  inherence_asymm: \<open>x \<triangleleft> y \<Longrightarrow> \<not> y \<triangleleft> x\<close> and
  (* Axion (7) on page 214 *)
  inherence_antitransitive: "\<lbrakk> x \<triangleleft> y ; y \<triangleleft> z \<rbrakk> \<Longrightarrow> \<not> x \<triangleleft> z"
begin \<^marker>\<open>tag aponly\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  To complete the axiomatization of the inherence relation with respect to
  the original theory presented in \cite{UFO}, we need to add a few more
  axioms to the @{locale inherence_base} theory, composing what we call the
  @{locale inherence_original} theory:
\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  \begin{axiom}[$@{thm_name inherence_irrefl}$\ufoformulafootnote{213}{5}]
  The inherence relation is an \gls{irreflexive-relation}:  
  \[ @{thm inherence_irrefl} \]
  \end{axiom}

  \begin{axiom}[$@{thm_name inherence_asymm}$\ufoformulafootnote{213}{6}]
  The inherence relation is an \gls{asymmetric-relation}:
  \[ @{thm inherence_asymm} \]
  \end{axiom}  

  \begin{axiom}[$@{thm_name inherence_antitransitive}$\ufoformulafootnote{214}{7}]
  The inherence relation is antitransitive:
  \[ @{thm inherence_antitransitive} \]
  \end{axiom}
\<close>
text_raw\<open>\par\<close>
end \<^marker>\<open>tag aponly\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  It is reasonable to expect that any chain \<open>m\<^sub>1 \<triangleleft> m\<^sub>2 \<triangleleft> m\<^sub>3 \<triangleleft> \<cdots>\<close> of moments will end up in a substantial,
  an ultimate bearer for the moments \<open>m\<^sub>1\<close>, \<open>m\<^sub>2\<close>, $\dots$ . Furthermore, only one such substantial should 
  exist for each moment, since a moment expresses, directly, or indirectly, a property of a single
  substantial. Under these assumptions, it is possible to refer to \emph{the ultimate bearer of}
  a moment in a determinate way.

  Similarly, a moment should have a determinate \emph{order}. Is it a first-order moment, a property
  of a substantial, or a second-order moment, a property of a property of a substantial, or a 
  third-order moment, etc. If a moment has only one order, then it makes sense to speak of
  \emph{the order of} a moment.

  Formally, we can define these concepts through the following functions: 
\<close>
text_raw\<open>\par\<close>
context \<^marker>\<open>tag aponly\<close> inherence_sig
begin \<^marker>\<open>tag aponly\<close> 

definition order :: \<open>'p \<Rightarrow> nat\<close> where \<open>order m \<equiv> THE n. has_order m n\<close>

definition ultimateBearer :: \<open>'p \<Rightarrow> 'p\<close> (\<open>!\<beta>\<close>)  
  where \<open>!\<beta> m \<equiv> THE x. is_an_ultimate_bearer_of x m\<close>

end \<^marker>\<open>tag aponly\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  However, even though the existence of a unique ultimate bearer and
  of a definite order for each moment are expected properties of the
  theory, they do not necessarily hold in the axiomatization provided
  in the original UFO work.  
\<close>
text_raw\<open>\par\<close>
context inherence_original
begin

lemmas all_inherence_original_axioms =
  all_inherence_base_axioms
  inherence_irrefl 
  inherence_asymm

end

subsection \<open>No Ultimate Bearer Anomaly\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  As explained in the previous section, in any reasonable formal theory of UFO moments and
  substantials, it is expected that every moment has an ultimate bearer. The existence of
  a moment for which no ultimate bearer exists can be considered an anomaly.  This anomaly 
  can be represented formally through the following logical proposition: 
\<close>
text_raw\<open>\par\<close>
context \<^marker>\<open>tag aponly\<close> inherence_sig
begin \<^marker>\<open>tag aponly\<close>

definition \<open>has_moment_without_ultimate_bearer \<longleftrightarrow>
            (\<exists>m \<in> \<M>. \<forall>y. \<not> is_an_ultimate_bearer_of y m)\<close>

end \<^marker>\<open>tag aponly\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  A theory in which this proposition holds is said to be a theory that has 
  the ``no ultimate bearer'' anomaly.  Considering the axioms introduced in 
  the @{locale inherence_base} locale
  as a minimum set of axioms for an inherence theory, the following lemma 
  describes a way to prove that the theory  has this property:
\<close>
text_raw\<open>\par\<close>
lemma (in inherence_base) 
    has_moment_without_ultimate_bearerI[intro]:
  assumes \<open>m \<in> \<M>\<close> \<open>\<And>n. \<exists>x. m \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> x\<close>
  shows \<open>has_moment_without_ultimate_bearer\<close>
proof -
  have A: \<open>x \<notin> \<S>\<close> if \<open>m \<triangleleft>\<triangleleft> x\<close> for x
  proof -
    obtain i where \<open>m \<triangleleft>\<triangleleft>\<^bsup>i\<^esup> x\<close> using \<open>m \<triangleleft>\<triangleleft> x\<close> by (meson tranclp_power)
    then obtain z where \<open>m \<triangleleft>\<triangleleft>\<^bsup>Suc i\<^esup> z\<close> using assms(2)by blast
    then have \<open>x \<triangleleft>\<triangleleft>\<^bsup>(Suc i) - i\<^esup> z\<close> 
      using inherence_mid_point \<open>m \<triangleleft>\<triangleleft>\<^bsup>i\<^esup> x\<close> Suc_leD by blast    
    then have \<open>x \<triangleleft> z\<close> by auto
    then show \<open>x \<notin> \<S>\<close> using \<S>_def \<M>_def by auto
  qed
  have \<open>\<forall>y. \<not> is_an_ultimate_bearer_of y m\<close>
  proof (intro allI notI)
    fix y
    assume \<open>is_an_ultimate_bearer_of y m\<close>
    then obtain \<open>y \<in> \<S>\<close> \<open>m \<triangleleft>\<triangleleft> y\<close> 
      using is_an_ultimate_bearer_of_def by (metis \<S>_E assms(1) rtranclpD)
    then show False using A by auto
  qed
  then show ?thesis 
    using \<open>m \<in> \<M>\<close>
    by (auto simp: has_moment_without_ultimate_bearer_def)
qed

lemma \<^marker>\<open>tag (proof) aponly\<close> (in inherence_base)
  has_moment_without_ultimate_bearerE[elim]:
  assumes \<open>has_moment_without_ultimate_bearer\<close>
  obtains m where \<open>m \<in> \<M>\<close> \<open>\<And>n. \<exists>x. m \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> x\<close>
proof -
  obtain m where \<open>m \<in> \<M>\<close> and m: \<open>\<And>y. is_an_ultimate_bearer_of y m\<Longrightarrow> False\<close>
    using assms by (auto simp: has_moment_without_ultimate_bearer_def)
  have A: \<open>x \<in> \<M>\<close> if \<open>(\<triangleleft>)\<^sup>*\<^sup>* m x\<close> for x
    using that is_an_ultimate_bearer_of_def m
    by (metis \<open>m \<in> \<M>\<close> \<S>_I rtranclpD trans_inheres_in_scope)
  have \<open>\<exists>x. m \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> x\<close> for n
  proof (induct \<open>n\<close>)
    case 0 then show \<open>?case\<close> by auto
  next
    case (Suc n) 
    then obtain x where \<open>m \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> x\<close> by blast
    have \<open>x \<in> \<M>\<close>
    proof (cases \<open>n = 0\<close>)
      assume \<open>n = 0\<close>
      then show \<open>x \<in> \<M>\<close> using \<open>m \<in> \<M>\<close> \<open>m \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> x\<close> by auto
    next
      assume \<open>n \<noteq> 0\<close>
      then have \<open>0 < n\<close> by auto
      then have \<open>m \<triangleleft>\<triangleleft> x\<close> using \<open>m \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> x\<close> by (meson tranclp_power)
      then show \<open>x \<in> \<M>\<close> using A by (simp add: tranclp_into_rtranclp)
    qed
    then obtain y where \<open>x \<triangleleft> y\<close> by blast
    then have \<open>m \<triangleleft>\<triangleleft>\<^bsup>Suc n\<^esup> y\<close> using \<open>m \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> x\<close> by auto
    then show \<open>?case\<close> by blast
  qed
  then show \<open>?thesis\<close> using that \<open>m \<in> \<M>\<close> by metis
qed 

subsection \<open>Cyclic Inherence Anomaly\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
   Another situation we do not expect to occur in a reasonable theory of UFO moments and
   substantials is one in which a moment inheres directly, or indirectly, into itself.
   Such situation would be as nonsensical as saying that there is property which is a
   property of itself, or a set that is member of itself.

   To define this anomaly formally, we first define the notion of a \emph{cyclic relation},
   were a relation here is taken to be a binary predicate. A binary predicate \<open>R\<close> is
   (or represents) a \emph{cyclic relation} if and only if there is some element that
   is related to itself by the transitive closure of \<open>R\<close>. Formally:
\<close>
text_raw\<open>\par\<close>
definition \<open>cyclic R \<equiv> \<exists>x. R\<^sup>+\<^sup>+ x x\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  It is easy to see that if the inherence relation is cyclic, then the theory
  has the ``no ultimate bearer'' anomaly, since any element related to itself
  by the transitive closure of the inherence relation would have at least one
  $n$-th level bearer for each natural number $n > 0$, as the following lemma
  proves:
\<close>
text_raw\<open>\par\<close>
lemma (in inherence_base) 
  cyclic_inherence_has_moment_witout_ultimate_bearer[intro!,simp]:
  \<open>cyclic (\<triangleleft>) \<Longrightarrow> has_moment_without_ultimate_bearer\<close>
proof -
  assume \<open>cyclic (\<triangleleft>)\<close>
  then obtain x where \<open>x \<triangleleft>\<triangleleft> x\<close> using cyclic_def  by metis
  then obtain n\<^sub>x where \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^sub>x\<^esup> x\<close> \<open>0 < n\<^sub>x\<close> using tranclp_power by force  
  have \<open>x \<in> \<M>\<close>
  proof -
    obtain y where \<open>x \<triangleleft> y\<close> \<open>y \<triangleleft>\<triangleleft> x\<close> by (metis \<open>x \<triangleleft>\<triangleleft> x\<close> converse_tranclpE)
    then show \<open>x \<in> \<M>\<close> using \<M>_def by blast  
  qed
  show \<open>?thesis\<close>
  proof 
    (intro has_moment_without_ultimate_bearerI[of \<open>x\<close>] \<open>x \<in> \<M>\<close>)
    fix n
    obtain a b 
      where n: \<open>n = a*n\<^sub>x + b\<close> \<open>b < n\<^sub>x\<close> 
      using \<open>0 < n\<^sub>x\<close> 
      by (metis le_less le_neq_implies_less 
                less_irrefl_nat mod_less_divisor 
                mod_mult2_eq mult.commute mult_0 
                split_mod)
    have \<open>x \<triangleleft>\<triangleleft>\<^bsup>a*n\<^sub>x\<^esup> x\<close>  
    proof (induct \<open>a\<close>)
      case 0 then show \<open>?case\<close> by auto
    next
      case (Suc a) 
      
      then have A: \<open>x \<triangleleft>\<triangleleft>\<^bsup>a * n\<^sub>x + n\<^sub>x\<^esup> x\<close>
        using \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^sub>x\<^esup> x\<close> by (metis relcomppI relpowp_add)
      have B: \<open>a * n\<^sub>x + n\<^sub>x = Suc a * n\<^sub>x\<close>  by simp
      show \<open>?case\<close> using A by (simp add: B)
    qed    
    obtain z where \<open>x \<triangleleft>\<triangleleft>\<^bsup>b\<^esup> z\<close> 
      using \<open>b < n\<^sub>x\<close> \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^sub>x\<^esup> x\<close>
      by (metis \<open>0 < n\<^sub>x\<close> less_imp_Suc_add nat.inject nat_neq_iff 
          relcomppE relpowp_E relpowp_add)
    then have \<open>x \<triangleleft>\<triangleleft>\<^bsup>a*n\<^sub>x + b\<^esup> z\<close> 
      using \<open>x \<triangleleft>\<triangleleft>\<^bsup>a*n\<^sub>x\<^esup> x\<close> by (metis relcomppI relpowp_add)
    then have \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> z\<close> using n by simp
    then show \<open>\<exists>z. x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> z\<close> by blast
  qed 
qed

text \<^marker>\<open>tag bodyonly\<close> \<open>
  The axioms described in the @{locale inherence_original} and @{locale inherence_base}
  locales, which corresponds to the axioms introduced in the original UFO theory, 
  do not exclude models in which the inherence is cyclic, as the following lemma
  shows:
\<close>
text_raw\<open>\par\<close>
lemma inherence_original_allows_cycles:
  \<open>\<exists>(\<W> :: nat set set) inheresIn. 
      inherence_original \<W> inheresIn \<and> cyclic inheresIn\<close>
proof -  
  let ?a = \<open>Suc undefined\<close>
  let ?b = \<open>Suc ?a\<close>
  let ?c = \<open>Suc ?b\<close>
  let \<open>?\<W>\<close> = \<open>{\<emptyset>,{?a,?b,?c :: nat}}\<close>
  define inheresIn where inheresIn[simp]: 
    \<open>inheresIn x y \<equiv> (x = ?a \<and> y = ?b) \<or> (x = ?b \<and> y = ?c) \<or> (x = ?c \<and> y = ?a)\<close> 
    for x y :: \<open>nat\<close>
  interpret possible_worlds \<open>?\<W>\<close> 
    apply (unfold_locales ; simp?)
    using inj_nat2Nat by auto
  have I_eq[simp]: \<open>\<P> = {?a,?b,?c}\<close> by (simp only: \<P>_def ; blast)
  have ed_iff[simp]: \<open>ed x y \<longleftrightarrow> x \<in> {?a,?b,?c} \<and> y \<in> {?a,?b,?c}\<close> for x y
    by (simp only: ed_def ; simp only: I_eq ; blast)

  interpret inherence_base \<open>?\<W>\<close> \<open>inheresIn\<close>
    apply (unfold_locales)
    subgoal G1 using I_eq by auto
    subgoal G2 by (simp only: ed_iff ; simp ; blast)
    by (simp ; presburger)

  interpret inherence_original \<open>?\<W>\<close> \<open>inheresIn\<close>
    by (unfold_locales ; simp ; linarith)        
          
  have \<open>inheresIn\<^sup>+\<^sup>+ ?a ?a\<close> 
  proof -
    obtain \<open>inheresIn ?a ?b\<close> \<open>inheresIn ?b ?c\<close> \<open>inheresIn ?c ?a\<close> by simp
    then show \<open>inheresIn\<^sup>+\<^sup>+ ?a ?a\<close> by (metis tranclp.simps)
  qed
  then have \<open>cyclic inheresIn\<close> by (auto simp: cyclic_def)
  then show \<open>?thesis\<close> using inherence_original_axioms by blast
qed

text \<^marker>\<open>tag bodyonly\<close> \<open>
  As a consequence, the ``ultimate bearer'' anomaly is present in the
  original theory:
\<close>
text_raw\<open>\par\<close>
lemma inherence_original_has_ultimate_bearer_problem:
  \<open>\<exists>(\<W> :: nat set set) inheresIn. 
     inherence_original \<W> inheresIn \<and>
     inherence_sig.has_moment_without_ultimate_bearer 
          \<W> inheresIn\<close>       
  using inherence_original_allows_cycles 
    inherence_base.cyclic_inherence_has_moment_witout_ultimate_bearer   
    inherence_original_def 
  by blast

locale \<^marker>\<open>tag aponly\<close> inherence_V2 = inherence_original +
  assumes no_inherence_cycles: \<open>\<not> (\<triangleleft>)\<^sup>+\<^sup>+ x x\<close>

begin \<^marker>\<open>tag aponly\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  We can eliminate cycles from the theory explicitly by including
  the following axiom:

\begin{axiom}[$@{thm_name no_inherence_cycles}$]
  No endurant must inhere, directly or indirectly, into itself:

  \[ @{thm no_inherence_cycles} \]
\end{axiom}

We call @{locale inherence_V2} the locale consisting on the axioms of
the original theory (@{locale inherence_original}) plus this axiom.

\<close>
text_raw\<open>\par\<close>
lemmas \<^marker>\<open>tag (proof) aponly\<close> all_inherence_V2_axioms =
    all_inherence_original_axioms no_inherence_cycles

lemma \<^marker>\<open>tag (proof) aponly\<close> no_inherence_cycles_2[simp,dest!]: 
  assumes \<open>(\<triangleleft>)\<^sup>+\<^sup>+ x x\<close>
  shows \<open>False\<close> 
  using assms no_inherence_cycles by simp

end \<^marker>\<open>tag (proof) aponly\<close>

subsection \<open>Infinite Inherence Chain Anomaly\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  Another peculiar situation that may appear in an inherence theory is one in
  which there is an infinite ascending chain of inhering endurants, e.g. there is an
  infinite sequence \<open>{e\<^sub>1, \<dots>}\<close> of endurants where, for every natural number
  \<open>i > 0\<close>, \<open>e\<^sub>i\<close> inheres in \<open>e\<^bsub>i+1\<^esub>\<close>. Formally: 
\<close>
text_raw\<open>\par\<close>
definition (in inherence_sig) inf_inh_asc_chain :: \<open>'p set \<Rightarrow> 'p \<Rightarrow> bool\<close> 
  where \<open>inf_inh_asc_chain X x \<equiv> infinite X \<and> (\<forall>y. y \<in> X \<longleftrightarrow> (\<triangleleft>)\<^sup>*\<^sup>* x y)\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  The existence of an infinite ascending inherence chain is represented
  by the following logical proposition:
\<close>
text_raw\<open>\par\<close>
definition (in inherence_sig) 
  \<open>has_inf_inh_asc_chain \<equiv> \<exists>X x. inf_inh_asc_chain X x\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  We use the notation \<open>\<Delta>\<^sup>\<beta> m s\<close> to represent the order of a moment \<open>m\<close>
  (if it is unique)
  with respect to \<open>s\<close>, where \<open>s\<close> is one of its indirect bearers.
  Formally:
\<close>
text_raw\<open>\par\<close>
definition (in inherence_sig) bearer_order :: \<open>'p \<Rightarrow> 'p \<Rightarrow> nat\<close> (\<open>\<Delta>\<^sup>\<beta>\<close>)
  where \<open>\<Delta>\<^sup>\<beta> m s \<equiv> THE n. m \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> s\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  We use the notation \<open>\<beta>* m\<close> to represent the set of direct or
  indirect bearers of the moment \<open>m\<close>:
\<close>
text_raw\<open>\par\<close>
definition (in inherence_sig) bearers :: \<open>'p \<Rightarrow> 'p set\<close> (\<open>\<beta>*\<close>)
  where \<open>\<beta>* m \<equiv> { s . m \<triangleleft>\<triangleleft> s }\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  The following lemma shows that, under the axioms of the 
  @{locale inherence_V2} locale, if a moment \<open>x\<close> inheres
  directly or indirectly into some \<open>y\<close>, it does so by a 
  unique number of inherence steps:
\<close>
text_raw\<open>\par\<close>
lemma (in inherence_V2) no_cycles:
  assumes \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> y\<close> \<open>x \<triangleleft>\<triangleleft>\<^bsup>n'\<^esup> y\<close>
  shows \<open>n = n'\<close>
proof (rule ccontr)
  assume \<open>n \<noteq> n'\<close>
  then consider 
      (lt) \<open>n' < n\<close> 
    | (gt) \<open>n < n'\<close>
    using nat_neq_iff by blast
  then obtain a b where AB: \<open>a < b\<close> \<open>x \<triangleleft>\<triangleleft>\<^bsup>a\<^esup> y\<close> \<open>x \<triangleleft>\<triangleleft>\<^bsup>b\<^esup> y\<close> by (meson assms) 
  then have \<open>y \<triangleleft>\<triangleleft>\<^bsup>b - a\<^esup> x\<close> 
    using inherence_mid_point
    by (meson no_inherence_cycles_2 order.strict_implies_order 
              tranclp_power zero_less_diff)
  then have \<open>x \<triangleleft>\<triangleleft> x\<close> 
    by (meson AB \<open>a < b\<close> relpowp_imp_rtranclp 
          rtranclp_tranclp_tranclp tranclp_power zero_less_diff)
  then show \<open>False\<close> using no_inherence_cycles by simp
qed

text \<^marker>\<open>tag bodyonly\<close> \<open>
  Consequently, as the following lemma proves, in the context of the
  @{locale inherence_V2} locale, for any direct or 
  indirect bearer of a moment \<open>m\<close> there is a definite number of
  steps by which \<open>m\<close> inheres in \<open>s\<close>:
\<close>
text_raw\<open>\par\<close>
lemma (in inherence_V2) bearer_order_ex1:
  assumes \<open>s \<in> \<beta>* m\<close>
  shows \<open>\<exists>!n. m \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> s\<close>
proof -
  have \<open>m \<triangleleft>\<triangleleft> s\<close> using assms bearers_def by auto
  then obtain n where \<open>m \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> s\<close> using tranclp_power by metis
  then have A: \<open>n' = n\<close> if \<open>m \<triangleleft>\<triangleleft>\<^bsup>n'\<^esup> s\<close> for n' using no_cycles that by blast
  then show \<open>?thesis\<close> by (intro ex1I[of _ \<open>n\<close>] \<open>m \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> s\<close> ; simp)
qed

text \<^marker>\<open>tag bodyonly\<close> \<open>
  Thus, in @{locale inherence_V2}, the notion of the order of a
  moment with respect to of its direct or indirect bearers is
  well defined an presents the following properties:
\<close>
text_raw\<open>\par\<close>
context inherence_V2
begin

lemma bearer_order_prop:
  assumes \<open>s \<in> \<beta>* m\<close>
  shows \<open>m \<triangleleft>\<triangleleft>\<^bsup>\<Delta>\<^sup>\<beta> m s\<^esup> s\<close>
  using theI' bearer_order_ex1 assms bearer_order_def 
  by metis

lemma bearer_order_eq:
  assumes \<open>m \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> s\<close>
  shows \<open>\<Delta>\<^sup>\<beta> m s = n\<close>
proof (cases \<open>n = 0\<close>)
  assume \<open>n = 0\<close>
  then have \<open>s = m\<close> using assms by auto
  have D0[simp]: \<open>\<Delta>\<^sup>\<beta> m m = 0\<close>
  proof (simp only: bearer_order_def ; intro the_equality ; simp?)
    fix n'
    assume as: \<open>m \<triangleleft>\<triangleleft>\<^bsup>n'\<^esup> m\<close>
    show \<open>n' = 0\<close>
    proof (rule ccontr)
      assume \<open>n' \<noteq> 0\<close>
      then have \<open>0 < n'\<close> by blast
      then have \<open>m \<triangleleft>\<triangleleft> m\<close> using as by (meson tranclp_power)
      then show \<open>False\<close> using no_inherence_cycles by simp
    qed
  qed
  show \<open>?thesis\<close> 
    using \<open>n = 0\<close> D0 \<open>s = m\<close> by simp
next
  assume \<open>n \<noteq> 0\<close>
  then have \<open>0 < n\<close> by blast
  then have \<open>m \<triangleleft>\<triangleleft> s\<close> using assms by (meson tranclp_power)
  then have \<open>s \<in> \<beta>* m\<close> by (simp add: bearers_def)
  then have \<open>m \<triangleleft>\<triangleleft>\<^bsup>\<Delta>\<^sup>\<beta> m s\<^esup> s\<close> using bearer_order_prop by simp
  then show \<open>?thesis\<close> using no_cycles assms by simp
qed

text \<^marker>\<open>tag bodyonly\<close> \<open>
  The expression @{term_type \<open>\<Delta>\<^sup>\<beta> x\<close>} is a function
  that associates direct or indirect bearers of \<open>x\<close>
  to its order. In @{locale inherence_V2}, this
  function is injective, i.e. no distinct
  direct or indirect bearers of some moment \<open>x\<close>
  have the same order:
\<close>
text_raw\<open>\par\<close>
lemma bearer_order_inj: \<open>inj_on (\<Delta>\<^sup>\<beta> x) (\<beta>* x)\<close>
proof
  fix y z
  assume \<open>y \<in> \<beta>* x\<close> \<open>z \<in> \<beta>* x\<close> and \<Delta>eq:  \<open>\<Delta>\<^sup>\<beta> x y = \<Delta>\<^sup>\<beta> x z\<close>
  have A: \<open>x \<triangleleft>\<triangleleft>\<^bsup>\<Delta>\<^sup>\<beta> x y\<^esup> y\<close> using \<open>y \<in> \<beta>* x\<close> bearer_order_prop by metis
  have \<open>x \<triangleleft>\<triangleleft>\<^bsup>\<Delta>\<^sup>\<beta> x z\<^esup> z\<close> using \<open>z \<in> \<beta>* x\<close> bearer_order_prop by metis
  then have B: \<open>x \<triangleleft>\<triangleleft>\<^bsup>\<Delta>\<^sup>\<beta> x y\<^esup> z\<close> using \<Delta>eq by simp
  then show \<open>y = z\<close> using nth_inherence_unique_cond A by simp
qed

end 

text \<^marker>\<open>tag bodyonly\<close> \<open>
  Leaving the revised locale @{locale inherence_V2} and the
  notion of the order of a moment aside for a moment, 
  we can show that in any theory that includes the basic axioms 
  of the @{locale inherence_base} locale, the existence of
  an infinite ascending inherence chain implies the presence
  of the ``ultimate bearer'' anomaly:
\<close>
text_raw\<open>\par\<close>
lemma (in inherence_base) 
  infinite_inherence_chain_imp_has_moment_without_ultimate_bearer:
  assumes \<open>has_inf_inh_asc_chain\<close>
  shows \<open>has_moment_without_ultimate_bearer\<close>
proof -
  text \<^marker>\<open>tag bodyonly\<close> \<open>
    By assumption there is an infinite ascending
    inherence chain \<open>X\<close> starting on some \<open>x\<close>:\<close>
  text_raw\<open>\par\<close>
  obtain X x where A: \<open>inf_inh_asc_chain X x\<close> 
    using assms by (auto simp: has_inf_inh_asc_chain_def)
  obtain \<open>infinite X\<close> \<open>\<forall>y. y \<in> X \<longleftrightarrow> (\<triangleleft>)\<^sup>*\<^sup>* x y\<close>
    using A inf_inh_asc_chain_def that by simp
  then have B: \<open>y \<in> X \<longleftrightarrow> (\<triangleleft>)\<^sup>*\<^sup>* x y\<close> for y by blast
  then have x_in[simp]: \<open>x \<in> X\<close> by simp
  have \<open>X = {x} \<union> \<beta>* x\<close>
  proof \<^marker>\<open>tag aponly\<close> (auto)    
    show \<open>y = x\<close> if as: \<open>y \<in> X\<close> \<open>y \<notin> \<beta>* x\<close> for y
    proof -
      have \<open>(\<triangleleft>)\<^sup>*\<^sup>* x y\<close> using as(1) B by simp
      then have \<open>x = y \<or> x \<triangleleft>\<triangleleft> y\<close> by (meson rtranclpD)
      then show \<open>y = x\<close> using as(2) bearers_def by auto
    qed
    show \<open>y \<in> X\<close> if as: \<open>y \<in> \<beta>* x\<close> for y using B as 
      by (auto simp: bearers_def)
  qed
  text \<^marker>\<open>tag bodyonly\<close> \<open>
    As a consequence, the set of direct or indirect 
    bearers of \<open>x\<close> is infinite:
  \<close>
  text_raw\<open>\par\<close>
  then have \<open>infinite (\<beta>* x)\<close> using \<open>infinite X\<close> by blast

  text \<^marker>\<open>tag bodyonly\<close> \<open>
    Thus, the set of direct or indirect 
    bearers of \<open>x\<close> forms a sequence 
    indexed by the bearer order: 
  \<close>
  text_raw\<open>\par\<close>
  have bearers_eq: 
    \<open>\<beta>* x = { #\<beta> x i | i . 0 < i \<and> i \<le> n }\<close> 
    if \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> y\<close> \<open>y \<in> \<S>\<close> for n y
  proof \<^marker>\<open>tag aponly\<close> (intro set_eqI ; simp add: bearers_def ; 
           intro iffI)       
    show \<open>\<exists>i. q = #\<beta> x i \<and> 0 < i \<and> i \<le> n\<close> if \<open>x \<triangleleft>\<triangleleft> q\<close> for q
    proof -
      obtain i where \<open>x \<triangleleft>\<triangleleft>\<^bsup>i\<^esup> q\<close> \<open>0 < i\<close> 
        using \<open>x \<triangleleft>\<triangleleft> q\<close> by (meson tranclp_power)
      then have  \<open>#\<beta> x i = q\<close> using nth_bearer_eqI by simp
      have \<open>i \<le> n\<close>
      proof (rule ccontr)
        assume \<open>\<not> i \<le> n\<close>
        then have \<open>n < i\<close> by auto
        then have AA: \<open>y \<triangleleft>\<triangleleft>\<^bsup>i - n\<^esup> q\<close> 
          using \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> y\<close> \<open>x \<triangleleft>\<triangleleft>\<^bsup>i\<^esup> q\<close> inherence_mid_point by simp
        have \<open>0 < i - n\<close> using \<open>n < i\<close> by auto
        then have \<open>y \<in> \<M>\<close> using inheres_in_by_scope AA by metis
        then show \<open>False\<close> using \<open>y \<in> \<S>\<close> by blast
      qed
      then show \<open>?thesis\<close> 
        using \<open>#\<beta> x i = q\<close> that \<open>0 < i\<close> by metis
    qed
    show \<open>x \<triangleleft>\<triangleleft> q\<close> if as: \<open>\<exists>i. q = #\<beta> x i \<and> 0 < i \<and> i \<le> n\<close> for q
    proof -      
      obtain i where \<open>q = #\<beta> x i\<close> \<open>0 < i\<close> \<open>i \<le> n\<close> using as by metis
      obtain y' where \<open>x \<triangleleft>\<triangleleft>\<^bsup>i\<^esup> y'\<close> 
        using \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> y\<close> \<open>i \<le> n\<close> 
        by (metis antisym_conv2 less_imp_Suc_add 
                  relcomppE relpowp_Suc_E relpowp_add)
      then have AA: \<open>x \<triangleleft>\<triangleleft>\<^bsup>i\<^esup> #\<beta> x i\<close> using nth_bearerI by metis
      then have BB: \<open>x \<triangleleft>\<triangleleft> #\<beta> x i\<close> by (meson \<open>0 < i\<close> tranclp_power)
      have \<open>#\<beta> x i = y'\<close> 
        using \<open>x \<triangleleft>\<triangleleft>\<^bsup>i\<^esup> y'\<close> nth_bearer_eqI by metis
      then show \<open>x \<triangleleft>\<triangleleft> q\<close> using \<open>q = #\<beta> x i\<close> BB by simp
    qed
  qed

  text \<^marker>\<open>tag bodyonly\<close> \<open>
   We can also infer that this set is finite if
   one of the (direct or indirect) bearers of \<open>x\<close> is a substantial:\<close>
  text_raw\<open>\par\<close>
  have finite_bearers: \<open>finite (\<beta>* x)\<close> if as: \<open>x \<triangleleft>\<triangleleft> y\<close> \<open>y \<in> \<S>\<close> for y
  proof -
    obtain n where \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> y\<close> using as(1) tranclp_power by metis
    then have \<open>\<beta>* x = { #\<beta> x i | i . 0 < i \<and> i \<le> n }\<close> 
      using as bearers_eq by simp
    then show \<open>?thesis\<close> by simp
  qed

  text \<^marker>\<open>tag bodyonly\<close> \<open>
     But, since the set of direct or indirect bearers
     of \<open>x\<close> is infinite, then all of its members must be
     moments, and since \<open>x\<close> inheres directly one at least
     one of those, \<open>x\<close> must also be a moment:\<close>
  text_raw\<open>\par\<close>
  have \<open>x \<in> \<M>\<close>
  proof -
    have \<open>X - {x} \<noteq> \<emptyset>\<close> using \<open>infinite X\<close> 
      by (metis finite.emptyI infinite_remove) 
    then obtain y where \<open>y \<in> X - {x}\<close> by blast
    then obtain \<open>y \<in> X\<close> \<open>y \<noteq> x\<close> by blast
    then have \<open>x \<triangleleft>\<triangleleft> y\<close> using \<open>y \<in> X\<close> by (metis B rtranclpD)
    then show \<open>x \<in> \<M>\<close> using trans_inheres_in_scope by blast
  qed

  text \<^marker>\<open>tag bodyonly\<close> \<open>
    Finally, we can prove that under the assumptions
    of this lemma, there is at least one moment (\<open>x\<close>)
    for which no ultimate bearer exists:\<close>
  text_raw\<open>\par\<close>
  show \<open>has_moment_without_ultimate_bearer\<close>  
  proof 
    (simp add: 
        has_moment_without_ultimate_bearer_def 
        is_an_ultimate_bearer_of_def ; 
        intro bexI[of _ \<open>x\<close>] \<open>x \<in> \<M>\<close> allI impI notI)
    fix y
    assume \<open>(\<triangleleft>)\<^sup>*\<^sup>* x y\<close> \<open>y \<in> \<S>\<close>
    then consider \<open>x = y\<close> | \<open>x \<triangleleft>\<triangleleft> y\<close> by (meson rtranclpD)
    then consider \<open>y \<in> \<M>\<close> | \<open>x \<triangleleft>\<triangleleft> y\<close> \<open>y \<in> \<S>\<close> 
      using trans_inheres_in_scope \<open>x \<in> \<M>\<close> by blast
    then have \<open>y \<in> \<M>\<close>
    proof (cases ; simp)
      assume \<open>x \<triangleleft>\<triangleleft> y\<close> \<open>y \<in> \<S>\<close>
      then have \<open>finite (\<beta>* x)\<close> using finite_bearers by simp
      then have \<open>False\<close> using \<open>infinite (\<beta>* x)\<close> by simp
      then show \<open>y \<in> \<M>\<close> by simp
    qed
    then show False using \<open>y \<in> \<S>\<close> \<S>_def by simp
  qed
qed

text \<^marker>\<open>tag bodyonly\<close> \<open>
  Using the previous lemmas, we can prove that the 
  revised locale @{locale inherence_V2} allows
  infinite ascending inherence chains to occur:
\<close>
text_raw\<open>\par\<close>
lemma inherence_V2_allows_infinite_inherence_chain:
  \<open>\<exists>(\<W> :: nat set set) inheresIn. 
        inherence_V2 \<W> inheresIn
      \<and> inherence_sig.has_inf_inh_asc_chain inheresIn\<close> 
proof -
  let \<open>?\<W>\<close> = \<open>{\<emptyset>,{x . undefined < x } :: nat set}\<close>  
  let \<open>?inheresIn\<close> = \<open>\<lambda>x y. undefined < x \<and> y = Suc x\<close>
  interpret possible_worlds \<open>?\<W>\<close> 
    using inj_nat2Nat by (unfold_locales ; simp? ; blast)        
  interpret inherence_original \<open>?\<W>\<close> \<open>?inheresIn\<close>
    by (unfold_locales ; simp add: ed_def \<P>_def)
  have A: \<open>x < y \<Longrightarrow> \<exists>k. 0 < k \<and> y = x + k\<close> for x y :: nat by presburger
  have B: \<open>inheres_in_trancl x y \<longleftrightarrow> undefined < x \<and> x < y\<close> for x y
    apply (intro iffI)
    subgoal
      apply (induct  rule: tranclp_induct)
      subgoal for z by presburger
      by simp
    subgoal 
      apply (elim conjE ; drule A[of x y] ; elim exE conjE ; hypsubst_thin)
      subgoal for k
        apply (induct k arbitrary: x ; simp)
        subgoal premises P for t u
          apply (cases \<open>0 < t\<close>)
          subgoal 
            apply (drule P(1)[OF P(2)])
            apply (rule tranclp.intros(2)[of _ _ \<open>u + t\<close>] ; simp)            
            by (simp add: P(2) trans_less_add1)
          using P by auto
        done
      done
    done
  have C[simp]: \<open>\<not> inheres_in_trancl x x\<close> for x 
    by (simp add: B)
        
  interpret inherence_V2 \<open>?\<W>\<close> \<open>?inheresIn\<close>
    apply (unfold_locales ; intro notI)
    by simp

  have \<open>R\<^sup>*\<^sup>* x y \<longleftrightarrow> x = y \<or> R\<^sup>+\<^sup>+ x y\<close> 
    for x y :: 'a and R 
    by (simp add: Nitpick.rtranclp_unfold)
  have D: \<open>?inheresIn\<^sup>*\<^sup>* = (\<lambda>x y. x = y \<or> undefined < x \<and> x < y)\<close>    
    apply (intro ext)
    by (simp only: Nitpick.rtranclp_unfold B)
        
  have \<open>has_inf_inh_asc_chain\<close>
    apply (simp add: has_inf_inh_asc_chain_def)
    apply (intro exI[of _ \<open>{x . undefined < x}\<close>])
    apply (intro exI[of _ \<open>Suc undefined\<close>])
    apply (auto simp add: inf_inh_asc_chain_def D)
    by (metis finite_nat_set_iff_bounded mem_Collect_eq 
        not_less_eq not_less_iff_gr_or_eq)
  then show \<open>?thesis\<close> using inherence_V2_axioms by auto
qed

text \<^marker>\<open>tag bodyonly\<close> \<open>
  Thus, the revised locale @{locale inherence_V2} still has
  the ``no ultimate bearer'' anomaly, despite 
  excluding cycles in the inherence relation:
\<close>
text_raw\<open>\par\<close>
lemma inherence_V2_has_ultimate_bearer_problem:
  \<open>\<exists>(\<W> :: nat set set) inheresIn. inherence_V2 \<W> inheresIn
      \<and> inherence_sig.has_moment_without_ultimate_bearer \<W> inheresIn\<close>
  using inherence_V2_allows_infinite_inherence_chain 
  inherence_base.infinite_inherence_chain_imp_has_moment_without_ultimate_bearer  
  inherence_original.axioms(1) inherence_V2.axioms(1) 
  by blast

locale \<^marker>\<open>tag aponly\<close> inherence_V3 = inherence_V2  +
  assumes no_infinite_inherence_chains: \<open>\<not> inf_inh_asc_chain X x\<close>
begin \<^marker>\<open>tag aponly\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  Again, we can revise the @{locale inherence_V2} locale by adding a axiom that
  excludes the existence of infinite ascending inherence chains, producing the
  locale @{locale inherence_V3}:

\begin{axiom}[$@{thm_name no_infinite_inherence_chains}$]

\[ @{thm no_infinite_inherence_chains} \]

\end{axiom}
\<close>
text_raw\<open>\par\<close>
lemmas \<^marker>\<open>tag aponly\<close> all_inherence_V3_axioms =
  all_inherence_V2_axioms no_infinite_inherence_chains

text \<^marker>\<open>tag bodyonly\<close> \<open>
  With the exclusion of infinite ascending inherence chains, the 
  ``no ultimate bearer'' anomaly ceases to be present, as shown
  in the following lemma:
\<close>
text_raw\<open>\par\<close>
lemma no_ultimate_bearer_problem: \<open>\<not> has_moment_without_ultimate_bearer\<close>
proof
  show \<open>False\<close> 
    when \<open>\<exists>m. inf_inh_asc_chain ({m} \<union> \<beta>* m) m\<close> 
    using no_infinite_inherence_chains that by metis
  assume \<open>has_moment_without_ultimate_bearer\<close>
  then obtain m 
    where \<open>m \<in> \<M>\<close> and A: \<open>\<And>n. \<exists>x. m \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> x\<close>
    using has_moment_without_ultimate_bearerE by metis
  show \<open>\<exists>m. inf_inh_asc_chain ({m} \<union> \<beta>* m) m\<close>
    apply (intro exI[of _ \<open>m\<close>] ; simp add: inf_inh_asc_chain_def)
    apply (intro conjI allI iffI disjCI ; (elim disjE)? ; simp?)
  proof  -
    have \<open>\<Delta>\<^sup>\<beta> m ` \<beta>* m = {n | n. 0 < n \<and> m \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> #\<beta> m n}\<close> 
    proof (auto simp: image_iff)
      show \<open>0 < \<Delta>\<^sup>\<beta> m y\<close> if \<open>y \<in> \<beta>* m\<close> for y
        using that bearer_order_prop bearers_def by fastforce
      show \<open>\<exists>z. m \<triangleleft>\<triangleleft>\<^bsup>\<Delta>\<^sup>\<beta> m y\<^esup> z\<close> if as1: \<open>y \<in> \<beta>* m\<close> for y using A by simp          
      show \<open>\<exists>x\<in>\<beta>* m. n = \<Delta>\<^sup>\<beta> m x\<close> if as2: \<open>0 < n\<close> \<open>m \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> #\<beta> m n\<close> for n
      proof (intro bexI[of _ \<open>#\<beta> m n\<close>]) 
        show \<open>n = \<Delta>\<^sup>\<beta> m (#\<beta> m n)\<close> using as2 bearer_order_eq that by auto
        show \<open>#\<beta> m n \<in> \<beta>* m\<close>
          using as2 bearers_def by (metis mem_Collect_eq tranclp_power)
      qed
    qed
    have \<open>\<Delta>\<^sup>\<beta> m ` \<beta>* m = UNIV - {0}\<close>
      apply (auto simp: image_iff set_eq_iff)
      subgoal 
        using bearer_order_prop bearer_order_eq bearers_def by fastforce
      subgoal for n 
        apply (intro bexI[of _ \<open>#\<beta> m n\<close>])
        subgoal using A by (metis bearer_order_eq nth_bearer_eqI)
        subgoal using A 
          by (metis inherence_sig.bearers_def 
                mem_Collect_eq nth_bearer_eqI tranclp_power)
        done
      done
    then have \<open>infinite (\<Delta>\<^sup>\<beta> m ` \<beta>* m)\<close> by simp
    then show \<open>infinite (\<beta>* m)\<close> by blast
    show \<open>(\<triangleleft>)\<^sup>*\<^sup>* m y\<close> if \<open>y \<in> \<beta>* m\<close> for y      
      using bearers_def that by auto      
    show \<open>y = m\<close> if \<open>y \<notin> \<beta>* m\<close> \<open>(\<triangleleft>)\<^sup>*\<^sup>* m y\<close> for y      
      by (metis bearers_def mem_Collect_eq rtranclpD that(1) that(2))      
  qed
qed

end \<^marker>\<open>tag aponly\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
 In fact, under the axioms of the @{locale inherence_base} locale, 
 the non-existence of a moment without an ultimate bearer is logically
 equivalent to the inherence being acyclic and not existing 
 infinite ascending inherence chains:
\<close>
text_raw\<open>\par\<close>
lemma (in inherence_base) no_ultimate_bearer_conditions:
  \<open>\<not> has_moment_without_ultimate_bearer \<longleftrightarrow> \<not> cyclic (\<triangleleft>) \<and> \<not>has_inf_inh_asc_chain\<close>
  (is \<open>\<not> ?A \<longleftrightarrow> \<not> ?B \<and> \<not> ?C\<close>)
proof -
  have R1: \<open>\<not> A \<longleftrightarrow> \<not> B \<and> \<not> C\<close> if \<open>B \<Longrightarrow> A\<close> \<open>C \<Longrightarrow> A\<close> \<open>\<lbrakk> A ; \<not> B \<rbrakk> \<Longrightarrow> C\<close> 
     for A B C using that by blast
  note R2 = R1[
       where ?A = \<open>?A\<close> and ?B = \<open>?B\<close> and ?C = \<open>?C\<close>,
       OF cyclic_inherence_has_moment_witout_ultimate_bearer
       infinite_inherence_chain_imp_has_moment_without_ultimate_bearer,
       simplified]
  show \<open>?thesis\<close>
  proof (intro R2)
    assume as: \<open>has_moment_without_ultimate_bearer\<close> \<open>\<not> cyclic (\<triangleleft>)\<close>
    interpret inherence_original \<open>\<W>\<close> \<open>inheresIn\<close> 
      apply(unfold_locales)
      subgoal for x using \<open>\<not> cyclic (\<triangleleft>)\<close> cyclic_def by blast
      subgoal for x using \<open>\<not> cyclic (\<triangleleft>)\<close> 
        by (meson cyclic_def tranclp.simps 
                  tranclp_into_tranclp2)
      subgoal for x y z using \<open>\<And>x. \<not> x \<triangleleft> x\<close> moment_non_migration by auto
      done
    interpret inherence_V2 \<open>\<W>\<close> \<open>inheresIn\<close>
      apply(unfold_locales)
      using \<open>\<not> cyclic (\<triangleleft>)\<close> cyclic_def by blast
    show \<open>has_inf_inh_asc_chain\<close> using as(1)      
      using has_inf_inh_asc_chain_def inherence_V2_axioms 
            inherence_V3.no_ultimate_bearer_problem 
            inherence_V3_axioms_def inherence_V3_def 
      by blast
  qed
qed

text \<^marker>\<open>tag bodyonly\<close> \<open>
   As the following lemmas prove, under the axioms of the @{locale inherence_base} locale,
   the non-existence of moments without ultimate bearers is also logically equivalent to
   the inherence relation being \emph{noetherian}, i.e. if the converse of the inherence
   relation is well-founded. Before we present the proof, we need to define to set of suborders of an endurant. 
  For any endurant \<open>x\<close>, the set of suborders of \<open>x\<close>, written as \<open>suborders x\<close>, is
  a set of natural numbers such that any member \<open>n\<close> is the order of \<open>x\<close> with respect
  to one of its direct or indirect bearers. Formally:
\<close>
text_raw\<open>\par\<close>
context \<^marker>\<open>tag aponly\<close> inherence_base
begin \<^marker>\<open>tag aponly\<close>

definition suborders :: \<open>'p \<Rightarrow> nat set\<close> where
  \<open>suborders x \<equiv> { n | n y . x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> y }\<close>

lemma \<^marker>\<open>tag (proof) aponly\<close> subordersI[intro!]: \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> y \<Longrightarrow> n \<in> suborders x\<close>
  using suborders_def by auto

lemma \<^marker>\<open>tag (proof) aponly\<close> subordersE[elim]: 
  assumes \<open>n \<in> suborders x\<close>
  obtains y where \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> y\<close>
  using assms suborders_def 
  by auto

text \<^marker>\<open>tag bodyonly\<close> \<open>
  In the context of the @{locale inherence_base} locale, for any endurant \<open>x\<close>,
  \<open>x\<close> has an ultimate bearer just in case its set of suborders is finite:
\<close>
text_raw\<open>\par\<close>
lemma has_ultimate_bearer_iff_suborders_finite:
  assumes \<open>x \<in> \<M>\<close>
  shows \<open>(\<exists>y. is_an_ultimate_bearer_of y x) \<longleftrightarrow> finite (suborders x)\<close>
proof 
  assume \<open>\<exists>y. is_an_ultimate_bearer_of y x\<close>
  then obtain y where \<open>is_an_ultimate_bearer_of y x\<close> 
    by blast
  then obtain \<open>x \<triangleleft>\<triangleleft> y\<close> \<open>y \<in> \<S>\<close> 
    using is_an_ultimate_bearer_of_def assms by (metis \<S>_E rtranclpD)
  then obtain n\<^sub>y where \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^sub>y\<^esup> y\<close> by (meson tranclp_power) 
  have \<open>\<not> y \<triangleleft> z\<close> for z using \<open>y \<in> \<S>\<close> by blast 
  then have \<open>\<not> y \<triangleleft>\<triangleleft> z\<close> for z by (meson tranclpD)
  then have A: \<open>n = 0\<close> if \<open>y \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> z\<close> for n z 
    by (meson neq0_conv that tranclp_power)
  have \<open>suborders x = { i . i \<le> n\<^sub>y }\<close>
  proof (rule ccontr)
    assume \<open>suborders x \<noteq> {i. i \<le> n\<^sub>y}\<close>
    then consider 
        (lt) n where \<open>n \<notin> suborders x\<close> \<open>n \<le> n\<^sub>y\<close> 
      | (gt) n where \<open>n \<in> suborders x\<close> \<open>n\<^sub>y < n\<close>       
      using suborders_def by fastforce
    then show \<open>False\<close>
    proof (cases)
      case (lt n)
      obtain k where \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> k\<close> 
        using \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^sub>y\<^esup> y\<close> \<open>n \<le> n\<^sub>y\<close> 
        by (metis antisym_conv2 less_imp_Suc_add 
                  relcomppE relpowp_Suc_E relpowp_add)
      then have \<open>n \<in> suborders x\<close> using subordersI by blast
      then show \<open>False\<close> using lt by simp
    next
      case (gt n)
      then obtain z where \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> z\<close> using subordersE by blast      
      then have \<open>y \<triangleleft>\<triangleleft>\<^bsup>n - n\<^sub>y\<^esup> z\<close> 
        using inherence_mid_point \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^sub>y\<^esup> y\<close> gt by auto
      then have \<open>n - n\<^sub>y = 0\<close> using A by metis
      then show \<open>False\<close> using \<open>n\<^sub>y < n\<close> by auto
    qed
  qed
  then show \<open>finite (suborders x)\<close> 
    by simp
next
  assume \<open>finite (suborders x)\<close>
  then obtain n where A: \<open>n \<in> suborders x\<close> \<open>\<And>m. m \<in> suborders x \<Longrightarrow> m \<le> n\<close>
    by (metis Max_ge Max_in emptyE 
              relpowp_0_I subordersI)
  then obtain y where \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> y\<close> by blast
  then have \<open>y \<in> \<E>\<close> 
    by (metis assms endurantI1 gr0I inheres_in_by_scope 
              nth_bearer_eqI zeroth_bearer)
  have \<open>y \<notin> \<M>\<close>
  proof
    assume \<open>y \<in> \<M>\<close>
    then obtain z where \<open>y \<triangleleft> z\<close> by blast
    then have \<open>x \<triangleleft>\<triangleleft>\<^bsup>(Suc n)\<^esup> z\<close> using \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> y\<close> by auto
    then have \<open>Suc n \<in> suborders x\<close> by blast
    then have \<open>Suc n \<le> n\<close> using A(2) by blast
    then show \<open>False\<close> by simp
  qed
  then have \<open>y \<in> \<S>\<close> using \<open>y \<in> \<E>\<close> by blast
  have \<open>x \<triangleleft>\<triangleleft> y\<close> using \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> y\<close> 
    by (metis \<open>y \<notin> \<M>\<close> assms relpowp_imp_rtranclp rtranclpD)
  then show \<open>\<exists>y. is_an_ultimate_bearer_of y x\<close> 
    using \<open>y \<in> \<S>\<close> is_an_ultimate_bearer_of_def      
      by (meson tranclp_into_rtranclp)
qed

text \<^marker>\<open>tag bodyonly\<close> \<open>
  Thus, in the same context, the non-existence of moments without ultimate bearers
  is logically equivalent to the well-foundness (\<open>wfP\<close>) of the converse of the
  inherence relation (\<open>(\<triangleleft>)\<inverse>\<inverse>\<close>), or, in other words, to the inherence relation
  being noetherian:
\<close>
text_raw\<open>\par\<close>
lemma no_ultimate_bearer_problem_eq_noetherian:
  shows \<open>\<not> has_moment_without_ultimate_bearer \<longleftrightarrow> wfP (\<triangleleft>)\<inverse>\<inverse>\<close> 
proof -
  have S1: \<open>\<not> has_moment_without_ultimate_bearer \<longleftrightarrow> 
            (\<forall>x \<in> \<M>. \<exists>y. is_an_ultimate_bearer_of y x)\<close>
    by (auto simp: has_moment_without_ultimate_bearer_def)
  show \<open>?thesis\<close> 
    when \<open>wfP (\<triangleleft>)\<inverse>\<inverse> \<longleftrightarrow> (\<forall>x. finite (suborders x))\<close> 
    using has_ultimate_bearer_iff_suborders_finite S1
    by (metis \<M>_def diff_is_0_eq finite_nat_set_iff_bounded 
          finite_nat_set_iff_bounded_le gr0I 
          mem_Collect_eq relpowp_E2 subordersE that)  
  have R1: \<open>wfP (\<triangleleft>)\<inverse>\<inverse>\<close> if as: \<open>\<forall>x. finite (suborders x)\<close> 
  proof (intro wfI_min[to_pred])
    fix x :: \<open>'p\<close> and Q
    assume \<open>x \<in> Q\<close>
    define X where \<open>X \<equiv> { n | y n . y \<in> Q \<and> x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> y }\<close>    
    have X_subset_suborder: \<open>X \<subseteq> suborders x\<close> 
      using X_def subordersI by blast
    then have \<open>finite X\<close> using infinite_super as by auto     
    define nmax where \<open>nmax \<equiv> Max X\<close>
    obtain nmax: \<open>nmax \<in> X\<close> \<open>\<And>n. n \<in> X \<Longrightarrow> n \<le> nmax\<close> 
      using \<open>finite X\<close> 
      by (metis (full_types, lifting) Max_ge Max_in X_def 
          \<open>x \<in> Q\<close> empty_Collect_eq nmax_def relpowp_0_I) 
    obtain z 
      where \<open>z \<in> Q\<close> \<open>x \<triangleleft>\<triangleleft>\<^bsup>nmax\<^esup> z\<close> using \<open>nmax \<in> X\<close> X_def by auto    
    have \<open>\<forall>y. (\<triangleleft>)\<inverse>\<inverse> y z \<longrightarrow> y \<notin> Q\<close>
    proof (auto)
      fix y
      assume \<open>z \<triangleleft> y\<close> \<open>y \<in> Q\<close>
      then have A: \<open>x \<triangleleft>\<triangleleft>\<^bsup>(Suc nmax)\<^esup> y\<close> using \<open>x \<triangleleft>\<triangleleft>\<^bsup>nmax\<^esup> z\<close> by auto
      then have B: \<open>Suc nmax \<in> suborders x\<close> using subordersI by blast
      have C: \<open>Suc nmax \<in> X\<close> using A X_def \<open>y \<in> Q\<close> by blast
      then have \<open>Suc nmax \<le> nmax\<close> using nmax(2) by simp
      then show \<open>False\<close> by simp
    qed
    then
    show \<open>\<exists>z\<in>Q. \<forall>y. (\<triangleleft>)\<inverse>\<inverse> y z \<longrightarrow> y \<notin> Q\<close> using \<open>z \<in> Q\<close> by blast      
  qed
  have R2: \<open>\<forall>x. finite (suborders x)\<close> if as: \<open>wfP (\<triangleleft>)\<inverse>\<inverse>\<close>
  proof (rule ccontr ; simp)
    assume \<open>\<exists>x. infinite (suborders x)\<close>
    then obtain x where \<open>infinite (suborders x)\<close> by blast
    have \<open>suborders x = UNIV\<close>
    proof (intro set_eqI ; simp)
      fix n
      show \<open>n \<in> suborders x\<close>
      proof (rule ccontr)
        assume \<open>n \<notin> suborders x\<close>
        then have \<open>\<not> x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> y\<close> for y by blast
        then have \<open>\<not> x \<triangleleft>\<triangleleft>\<^bsup>n'\<^esup> y\<close> if \<open>n \<le> n'\<close>  for y n'           
          by (metis antisym_conv2 less_imp_Suc_add relcomppE relpowp_Suc_E 
                    relpowp_add that) 
        then have \<open>n' < n\<close> if \<open>n' \<in> suborders x\<close> for n'
          using subordersE that by (meson leI)
        then have \<open>finite(suborders x)\<close>
          using bounded_nat_set_is_finite by blast
        then show \<open>False\<close> using \<open>infinite (suborders x)\<close> by simp
      qed
    qed    
    then have sb_ex: \<open>\<exists>y. x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> y\<close> for n using subordersE by blast
    have sb_ex1: \<open>\<exists>!y. x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> y\<close> for n 
    proof (intro ex_ex1I sb_ex)
      fix a b
      assume \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> a\<close> \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> b\<close>
      then show \<open>a = b\<close> using nth_inherence_unique_cond by simp
    qed
    then obtain f where f: \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> f n\<close> for n by moura              
    have f_suc: \<open>f n \<triangleleft> f (Suc n)\<close> for n
    proof -
      obtain AA: \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> f n\<close> \<open>x \<triangleleft>\<triangleleft>\<^bsup>(Suc n)\<^esup> f (Suc n)\<close> using f by metis
      obtain k where \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> k\<close> \<open>k \<triangleleft> f (Suc n)\<close> using AA(2) by auto
      then have \<open>k = f n\<close> 
        using nth_inherence_unique_cond AA(1) by blast
      then show \<open>?thesis\<close> using \<open>k \<triangleleft> f (Suc n)\<close> by simp
    qed

    define X where \<open>X \<equiv> { f n | n . True }\<close>
    have \<open>x \<in> X\<close> using X_def f 
      by (metis (mono_tags, lifting) CollectI relpowp.simps(1))
    obtain z 
      where \<open>z \<in> X\<close> and z: \<open>\<And>y. z \<triangleleft> y \<Longrightarrow> y \<notin> X\<close> 
      using wfE_min[to_pred,OF as] \<open>x \<in> X\<close> by (simp ; metis)
    then obtain n\<^sub>z where \<open>z = f n\<^sub>z\<close> using X_def by blast
    then have \<open>z \<triangleleft> f (Suc n\<^sub>z)\<close> using f_suc by simp
    then show \<open>False\<close> using z X_def by auto
  qed
  then show \<open>wfP (\<triangleleft>)\<inverse>\<inverse> \<longleftrightarrow> (\<forall>x. finite (suborders x))\<close> 
    using R1 by metis
qed
   
end

subsection \<open>Finite-Chain Inherence\<close>

locale \<^marker>\<open>tag aponly\<close> noetherian_inherence = inherence_base +
  assumes inherence_is_noetherian[intro!,simp]: \<open>wfP (\<triangleleft>)\<inverse>\<inverse>\<close> 
begin

text \<^marker>\<open>tag bodyonly\<close> \<open>
  Since under the axioms of the @{locale inherence_base} locale, non-existence of the
  ``no ultimate bearer'' anomaly is equivalent to the inherence relation being
  noetherian, let's consider an inherence theory, called @{locale noetherian_inherence}
  that simply adds the following axiom to @{locale inherence_base}:
  
\begin{axiom}[$@{thm_name inherence_is_noetherian}$]

The inherence relation should be noetherian, which means that its converse should
be well-founded:

\[ @{thm inherence_is_noetherian } \]

This means that for any non-empty set \<open>Q\<close> of particulars there is at least one member
\<open>z\<close> of \<open>Q\<close> such that if \<open>z\<close> inheres in some endurant \<open>y\<close> then \<open>y\<close> is not in \<open>Q\<close>:

\[ @{thm inherence_is_noetherian[simplified wfP_eq_minimal,rule_format,simplified]} \]

\end{axiom}
\<close>
text_raw\<open>\par\<close>
lemmas \<^marker>\<open>tag aponly\<close> just_noetherian_inherence_axioms = 
    inherence_is_noetherian

lemmas \<^marker>\<open>tag aponly\<close> all_noetherian_inherence_axioms = 
    all_inherence_base_axioms just_noetherian_inherence_axioms

text \<^marker>\<open>tag bodyonly\<close> \<open>
  Under this axiom, the inherence relation is acyclic:
\<close>
text_raw\<open>\par\<close>
lemma inherence_is_acyclic[intro!]: \<open>acyclicP (\<triangleleft>)\<close>
  using acyclicP_converse wfP_acyclicP inherence_is_noetherian 
  by metis

text \<^marker>\<open>tag bodyonly\<close> \<open>
  This axiom also implies the axioms stated in the original theory, such as:    
\<close>
text_raw \<^marker>\<open>tag bodyonly\<close> \<open>\begin{itemize}\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
 \item Inherence is irreflexive (axiom 5 on page 213, \cite{UFO}):
\<close>
  
lemma inherence_is_irrefl: \<open>\<not> x \<triangleleft> x\<close>   
  by (metis inherence_is_acyclic acyclic_irrefl[to_pred] 
            irreflp_def tranclp.r_into_trancl)

text \<^marker>\<open>tag bodyonly\<close> \<open>
 \item Inherence is asymmetric (axiom 6 on page 213, \cite{UFO}):
\<close>
text_raw\<open>\par\<close>
lemma inherence_is_asymm: \<open>x \<triangleleft> y \<Longrightarrow> \<not> y \<triangleleft> x\<close>
  using tranclp_trans inherence_is_acyclic acyclic_irrefl[to_pred] 
        irreflp_def tranclp.r_into_trancl
  by metis

text \<^marker>\<open>tag bodyonly\<close> \<open>
 \item Inherence is antitransitive (axiom 7 on page 214, \cite{UFO}):
\<close>
text_raw\<open>\par\<close>
lemma inherence_antitransitive_V1: \<open>\<lbrakk> x \<triangleleft> y ; y \<triangleleft> z \<rbrakk> \<Longrightarrow> \<not> x \<triangleleft> z\<close>  
  using inherence_is_irrefl inherence_is_asymm moment_non_migration 
  by metis


text_raw \<^marker>\<open>tag bodyonly\<close> \<open>\end{itemize}\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  Under this axiom, all the expected properties of the inherence relation hold:
\<close>

text_raw \<^marker>\<open>tag bodyonly\<close> \<open>\begin{itemize}\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  \item Every moment has a unique order with respect to each of its bearers:
\<close>
text_raw\<open>\par\<close>
lemma \<^marker>\<open>tag (proof) aponly\<close> unique_order: 
  \<open>n = n'\<close> if assms: \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> y\<close> \<open>x \<triangleleft>\<triangleleft>\<^bsup>n'\<^esup> y\<close>
proof \<^marker>\<open>tag aponly\<close> (rule ccontr)
  assume \<open>n \<noteq> n'\<close>
  have R: \<open>False\<close> if as: \<open>x \<triangleleft>\<triangleleft>\<^bsup>a\<^esup> y\<close> \<open>x \<triangleleft>\<triangleleft>\<^bsup>b\<^esup> y\<close> \<open>a < b\<close> for x y a b
  proof -
    have \<open>a \<le> b\<close> using \<open>a < b\<close> by auto
    then have \<open>y \<triangleleft>\<triangleleft>\<^bsup>b - a\<^esup> y\<close> using inherence_mid_point as by metis
    then have \<open>y \<triangleleft>\<triangleleft> y\<close> using \<open>a < b\<close> 
      by (meson tranclp_power zero_less_diff)
    then have \<open>cyclic (\<triangleleft>)\<close> using cyclic_def by auto
    then show \<open>False\<close> 
      using cyclic_inherence_has_moment_witout_ultimate_bearer 
        no_ultimate_bearer_problem_eq_noetherian 
      by blast
  qed
  consider \<open>n < n'\<close> | \<open>n' < n\<close>  using \<open>n \<noteq> n'\<close> nat_neq_iff by blast
  then show \<open>False\<close> by (cases ; auto intro: R assms)    
qed

text \<^marker>\<open>tag bodyonly\<close> \<open>\item Every moment has an ultimate bearer:\<close>
text_raw\<open>\par\<close>
lemma \<^marker>\<open>tag (proof) aponly\<close>ultimate_bearer_ex1I: 
  \<open>\<exists>!s. x \<triangleleft>\<triangleleft> s \<and> s \<in> \<S>\<close> 
  (is \<open>\<exists>!s. ?P s\<close>) 
  if \<open>x \<in> \<M>\<close>
proof \<^marker>\<open>tag aponly\<close> -
  have R1: \<open>\<exists>s. ?P s\<close>
  proof -
    have \<open>\<not>(\<forall>n. \<exists>y. x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> y)\<close>     
      using that no_ultimate_bearer_problem_eq_noetherian
      inherence_is_noetherian has_moment_without_ultimate_bearerI 
      has_moment_without_ultimate_bearerE
      by meson
    then have A: \<open>\<exists>n. \<forall>y. \<not> x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> y\<close> by blast
    define N where \<open>N = { n . \<forall>y. \<not> x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> y }\<close>
    then have \<open>N \<noteq> \<emptyset>\<close> using A by blast
    define nmin where \<open>nmin \<equiv> LEAST n. \<forall>y. \<not> x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> y\<close> 
                  (is \<open>nmin \<equiv> LEAST n. ?Q n\<close>)
    have \<open>\<exists>n. ?Q n\<close> using A by blast
    then have B: \<open>\<not> x \<triangleleft>\<triangleleft>\<^bsup>nmin\<^esup> y\<close> for y
      using LeastI_ex[of \<open>?Q\<close>] nmin_def by metis
    have C: \<open>nmin \<le> n\<close> if \<open>?Q n\<close> for n
      using Least_le[of \<open>?Q\<close>] nmin_def that by metis
    have D: \<open>0 < nmin\<close> using B  by fastforce
    then obtain nn where nn: \<open>nmin = Suc nn\<close> using Suc_pred' by blast
    then have \<open>\<not> ?Q nn\<close> using C[of \<open>nn\<close>]
      using Suc_n_not_le_n by blast
    then obtain y where E: \<open>x \<triangleleft>\<triangleleft>\<^bsup>nn\<^esup> y\<close> by blast
    then have \<open>y \<in> \<E>\<close> 
      using inheres_in_by_scope that
      by (metis endurantI1 nth_bearer_eqI nth_bearer_range')
    have \<open>\<not> y \<triangleleft> z\<close> for z
    proof
      assume \<open>y \<triangleleft> z\<close>
      then have \<open>x \<triangleleft>\<triangleleft>\<^bsup>Suc nn\<^esup> z\<close> using E by auto
      then show \<open>False\<close> using B nn by simp
    qed
    then have \<open>y \<in> \<S>\<close> using \<open>y \<in> \<E>\<close> \<S>_I by auto
    then show \<open>?thesis\<close> 
      using E by (metis \<S>_E relpowp_imp_rtranclp rtranclpD that)
  qed
  have R2: \<open>z = y\<close> if as: \<open>x \<triangleleft>\<triangleleft> z\<close> \<open>z \<in> \<S>\<close> \<open>x \<triangleleft>\<triangleleft> y\<close> \<open>y \<in> \<S>\<close> for z y
  proof -
    obtain n\<^sub>z where Z: \<open>0 < n\<^sub>z\<close> \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^sub>z\<^esup> z\<close> 
      using \<open>x \<triangleleft>\<triangleleft> z\<close> tranclp_power by metis
    obtain n\<^sub>y where Y: \<open>0 < n\<^sub>y\<close> \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^sub>y\<^esup> y\<close> 
      using \<open>x \<triangleleft>\<triangleleft> y\<close> tranclp_power by metis
    have A: \<open>a = b\<close> if \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> a\<close> \<open>x \<triangleleft>\<triangleleft>\<^bsup>n'\<^esup> b\<close> \<open>n \<le> n'\<close> \<open>a \<in> \<S>\<close> for n n' a b
    proof -
      have AA: \<open>a \<triangleleft>\<triangleleft>\<^bsup>n' - n\<^esup> b\<close> using that inherence_mid_point by simp
      have \<open>n = n'\<close>
      proof (rule ccontr)
        assume \<open>n \<noteq> n'\<close>
        then have \<open>n < n'\<close> using \<open>n \<le> n'\<close> by auto
        then have \<open>a \<triangleleft>\<triangleleft> b\<close> using AA 
          by (meson \<S>_E inheres_in_by_scope that(4) zero_less_diff)
        then obtain k where \<open>a \<triangleleft> k\<close> 
          using \<open>a \<in> \<S>\<close> trans_inheres_in_scope by blast
        then have \<open>a \<in> \<M>\<close> by blast
        then show \<open>False\<close> using \<open>a \<in> \<S>\<close> \<S>_E by blast
      qed
      then show \<open>a = b\<close> using AA by simp
    qed
    consider \<open>n\<^sub>z \<le> n\<^sub>y\<close> | \<open>n\<^sub>y \<le> n\<^sub>z\<close> using nat_le_linear by blast
    then show \<open>?thesis\<close> 
      by (cases ; insert A Y(2) Z(2) that(2,4) ; auto) 
  qed
  then show \<open>?thesis\<close> using ex_ex1I[OF R1] by metis
qed

lemma \<^marker>\<open>tag (proof) aponly\<close> order_ultimate_bearer_ex1I: \<open>\<exists>!(n,y). y \<notin> \<M> \<and> x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> y\<close> 
proof(cases \<open>x \<in> \<M>\<close>)
  assume \<open>x \<notin> \<M>\<close>
  show \<open>?thesis\<close> 
  proof (intro ex1I[of _ \<open>(0,x)\<close>] ; auto simp: \<open>x \<notin> \<M>\<close>)
    fix y n
    assume \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> y\<close>    
    show \<open>n = 0\<close>
    proof (rule ccontr)
      assume \<open>n \<noteq> 0\<close>
      then obtain \<open>x \<in> \<M>\<close> using \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> y\<close> inheres_in_by_scope by blast
      then show \<open>False\<close> using \<open>x \<notin> \<M>\<close> by simp
    qed
    then show \<open>y = x\<close> using \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> y\<close> by simp
  qed
next
  assume \<open>x \<in> \<M>\<close>
  then have A: \<open>\<exists>!s. x \<triangleleft>\<triangleleft> s \<and> s \<in> \<S>\<close> using ultimate_bearer_ex1I by simp
  then obtain s where B: \<open>x \<triangleleft>\<triangleleft> s\<close> \<open>s \<in> \<S>\<close> by blast
  then have \<open>s \<notin> \<M>\<close> by blast
  obtain n where C: \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> s\<close> \<open>0 < n\<close> using tranclp_power B(1) by metis
  have n_unique: \<open>n = n'\<close> if as: \<open>x \<triangleleft>\<triangleleft>\<^bsup>n'\<^esup> s'\<close> \<open>s' \<in> \<S>\<close> for n' s'
  proof -
    have \<open>s = s'\<close> 
      using A B as by (metis \<S>_E \<open>x \<in> \<M>\<close> relpowp_imp_rtranclp rtranclpD) 
    then have AA: \<open>x \<triangleleft>\<triangleleft>\<^bsup>n'\<^esup> s\<close> using as(1) by simp
    then show \<open>n = n'\<close> using C unique_order by simp
  qed
  show \<open>\<exists>!(n,y). y \<notin> \<M> \<and> x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> y\<close>
  proof (auto intro!: ex1I[of _ \<open>(n,s)\<close>] simp: \<open>s \<notin> \<M>\<close> \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> s\<close>)
    fix n' y
    assume \<open>y \<notin> \<M>\<close> \<open>x \<triangleleft>\<triangleleft>\<^bsup>n'\<^esup> y\<close>
    then have \<open>n' \<noteq> 0\<close> using \<open>x \<in> \<M>\<close> A by auto
    then have \<open>0 < n'\<close> by auto
    then have \<open>x \<triangleleft>\<triangleleft> y\<close> using \<open>x \<triangleleft>\<triangleleft>\<^bsup>n'\<^esup> y\<close> tranclp_power by metis
    then have \<open>y \<in> \<E>\<close> 
      using \<open>x \<triangleleft>\<triangleleft>\<^bsup>n'\<^esup> y\<close> \<open>0 < n'\<close> inheres_in_by_scope by metis
    then have \<open>y \<in> \<S>\<close> using \<open>y \<notin> \<M>\<close> by blast
    then show \<open>n' = n\<close>      using n_unique \<open>x \<triangleleft>\<triangleleft>\<^bsup>n'\<^esup> y\<close> by simp
    show \<open>y = s\<close> by (metis C(1) \<open>n' = n\<close> \<open>x \<triangleleft>\<triangleleft>\<^bsup>n'\<^esup> y\<close> nth_bearer_eqI)
  qed 
qed

text \<^marker>\<open>tag bodyonly\<close> \<open>\item The order of a moment is well defined:\<close>
text_raw\<open>\par\<close>
lemma order_eq_simp: 
  assumes \<open>x \<in> \<E>\<close>
  shows \<open>order x = n \<longleftrightarrow> (\<exists>y. y \<in> \<S> \<and> x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> y)\<close>
proof -
  have A: \<open>\<exists>!n. has_order x n\<close>
    using assms
    by (metis \<S>_I all_noetherian_inherence_axioms(5) 
         has_moment_without_ultimate_bearer_def 
         no_ultimate_bearer_problem_eq_noetherian  
         is_an_ultimate_bearer_of_def rtranclp.rtrancl_refl 
         ultimate_bearer_unique_order)
  then have B: \<open>order x = n\<close> if \<open>has_order x n\<close> for n 
    using order_def the1_equality that by metis
  have C: \<open>has_order x (order x)\<close> using the1I2 A order_def by metis
  have D: \<open>has_order x n\<close> if \<open>order x = n\<close> for n using that C A by metis
  then have E: \<open>order x = n \<longleftrightarrow> has_order x n\<close> for n using B by metis
  show ?thesis
    apply (simp add: E has_order_def is_an_ultimate_bearer_of_def)
    apply (intro iffI ; elim exE conjE)
    subgoal by blast
    subgoal for y by (intro exI[of _ y] conjI ; simp add: relpowp_imp_rtranclp)
    done
qed

text \<^marker>\<open>tag bodyonly\<close> \<open>\item The ultimate bearer of an endurant is well defined:\<close>
text_raw\<open>\par\<close>
lemma ultimate_bearer_eq_simp: 
  assumes \<open>x \<in> \<E>\<close>
  shows \<open>!\<beta> x = y \<longleftrightarrow> y \<in> \<S> \<and> (\<triangleleft>)\<^sup>*\<^sup>* x y\<close>  
proof -
  have A: \<open>\<exists>!z. is_an_ultimate_bearer_of z x\<close>
    using assms apply (cases x)
    subgoal S
      apply (intro ex1I[of _ x] ; simp add: is_an_ultimate_bearer_of_def)      
      by (metis inherence_sig.\<S>_E rtranclpD trans_inheres_in_scope)
    subgoal M premises p 
      supply R1 = ultimate_bearer_ex1I[OF p]
      apply (rule ex1E[OF R1] ; elim conjE)
      subgoal for z
        apply (intro ex1I[of _ z])
        subgoal G1
          apply (thin_tac X for X)
          by (simp add: is_an_ultimate_bearer_of_def[of z x])
        subgoal premises P for q
          using G1 P(1) P(2) P(3) P(4) assms ultimate_bearer_unique 
          by blast
        done
      done
    done
  note ultimateBearer_def[of x]
  note B = the1_equality[
            OF A, of y, simplified ultimateBearer_def[symmetric]]
  note C = the1I2[of "\<lambda>z. is_an_ultimate_bearer_of z x"
                 , simplified ultimateBearer_def[symmetric]
                 , where ?Q="\<lambda>b.  (b = y) = (y \<in> \<S> \<and> (\<triangleleft>)\<^sup>*\<^sup>* x y)" 
                 , OF A]
  show ?thesis
    apply (intro C)
    subgoal for z using A by (auto simp add: is_an_ultimate_bearer_of_def)
    done
qed
                           
lemma  \<^marker>\<open>tag (proof) aponly\<close>
  assumes \<open>x \<in> \<E>\<close>
  shows ultimate_bearer_and_order[intro!]: \<open>x \<triangleleft>\<triangleleft>\<^bsup>order x\<^esup> !\<beta> x\<close>
  and ultimate_bearer_is_not_a_moment[simp]: \<open>!\<beta> x \<notin> \<M>\<close>    
  subgoal G1
    using assms
    by (metis order_eq_simp relpowp_imp_rtranclp ultimate_bearer_eq_simp)
  subgoal G2
    using assms by (meson \<S>_E ultimate_bearer_eq_simp)
  done

text \<^marker>\<open>tag bodyonly\<close> \<open>\item The ultimate bearer is a substantial:\<close>
text_raw\<open>\par\<close>
lemma ultimate_bearer_substantial[simp]: \<open>x \<in> \<E> \<Longrightarrow> !\<beta> x \<in> \<S>\<close>  
  using ultimate_bearer_eq_simp by blast

text \<^marker>\<open>tag bodyonly\<close> \<open>\item If a moment inhere directly or indirectly into another endurant,
   then they both have the same ultimate bearer:\<close>
text_raw\<open>\par\<close>
lemma ultimate_bearer_eqI1: \<open>!\<beta> x = !\<beta> y\<close> if as: \<open>x \<triangleleft>\<triangleleft> y\<close>
proof \<^marker>\<open>tag aponly\<close> -
  obtain \<open>x \<in> \<M>\<close> \<open>y \<in> \<E>\<close> using as trans_inheres_in_scope by blast
  then have \<open>x \<in> \<E>\<close> by blast
  obtain n\<^sub>x where A: \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^sub>x\<^esup> y\<close> \<open>0 < n\<^sub>x\<close> 
    using as tranclp_power by metis
  then have B: \<open>(\<triangleleft>)\<^sup>*\<^sup>* x y\<close> using rtranclp_power by metis
  obtain C: \<open>y \<triangleleft>\<triangleleft>\<^bsup>order y\<^esup> !\<beta> y\<close> \<open>!\<beta> y \<notin> \<M>\<close>
    using ultimate_bearer_and_order ultimate_bearer_is_not_a_moment 
          \<open>x \<in> \<E>\<close> \<open>y \<in> \<E>\<close> 
    by auto
  then have D: \<open>(\<triangleleft>)\<^sup>*\<^sup>* y (!\<beta> y)\<close> using rtranclp_power by metis
  then have E: \<open>(\<triangleleft>)\<^sup>*\<^sup>* x (!\<beta> y)\<close> using rtranclp_trans B by metis
  then show \<open>!\<beta> x = !\<beta> y\<close>
    by (subst ultimate_bearer_eq_simp[OF \<open>x \<in> \<E>\<close>,of \<open>!\<beta> y\<close>] 
       ; intro conjI ; simp add: C(2) \<open>y \<in> \<E>\<close>)    
qed

lemma \<^marker>\<open>tag (proof) aponly\<close> order_diff: \<open>n = order y - order x\<close> if assms: \<open>y \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> x\<close> 
proof (cases \<open>n = 0\<close>)
  assume \<open>n = 0\<close>
  then have \<open>x = y\<close> using assms by auto
  then show \<open>?thesis\<close> using \<open>n = 0\<close> by simp
next
  assume \<open>n \<noteq> 0\<close>
  then have \<open>0 < n\<close> by blast  
  then have \<open>y \<triangleleft>\<triangleleft> x\<close> using assms tranclp_power by metis
  then have byx[simp]: \<open>!\<beta> y = !\<beta> x\<close> using ultimate_bearer_eqI1 by simp
  have \<open>y \<in> \<E>\<close> using \<open>y \<triangleleft>\<triangleleft> x\<close> by (meson endurantI1 trans_inheres_in_scope)
  then have ordY: \<open>y \<triangleleft>\<triangleleft>\<^bsup>order y\<^esup> !\<beta> y\<close> using ultimate_bearer_and_order by blast
  then have A: \<open>y \<triangleleft>\<triangleleft>\<^bsup>order y\<^esup> !\<beta> x\<close> by simp
  have \<open>x \<in> \<E>\<close>  using \<open>y \<triangleleft>\<triangleleft> x\<close> by (meson endurantI1 trans_inheres_in_scope)
  then have B: \<open>x \<triangleleft>\<triangleleft>\<^bsup>order x\<^esup> !\<beta> x\<close> by auto
  then have C: \<open>y \<triangleleft>\<triangleleft>\<^bsup>n + order x\<^esup> !\<beta> x\<close>     
    by (metis relcompp.relcompI assms relpowp_add) 
  then have D: \<open>order y = n + order x\<close> using unique_order ordY by simp
  then show \<open>n = order y - order x\<close> by presburger
qed    

lemma \<^marker>\<open>tag (proof) aponly\<close> order_le: \<open>order x < order y\<close> if assms: \<open>y \<triangleleft>\<triangleleft> x\<close>
proof -
  obtain n where A: \<open>0 < n\<close> \<open>y \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> x\<close> by (meson assms tranclp_power)    
  then have \<open>n = order y - order x\<close> using order_diff by simp
  then have \<open>0 < order y - order x\<close> using A by presburger
  then show \<open>?thesis\<close> by presburger
qed

lemma \<^marker>\<open>tag (proof) aponly\<close> order_le1: 
  \<open>order x \<le> order y\<close> if assms: \<open>(\<triangleleft>)\<^sup>*\<^sup>* y x\<close>   
  by (metis Nitpick.rtranclp_unfold eq_refl less_imp_le_nat order_le that)

lemma \<^marker>\<open>tag (proof) aponly\<close> order_le2: 
  \<open>order x < order y\<close> if assms: \<open>y \<triangleleft> x\<close>
  using order_le tranclp.intros(1) assms by metis

lemma \<^marker>\<open>tag (proof) aponly\<close> inheres_in_by_order:  
  \<open>n \<le> order x\<close> if assms: \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> y\<close>
proof (rule ccontr)
  have \<open>order y \<le> order x\<close> using order_le1 assms rtranclp_power by metis 
  assume \<open>\<not> n \<le> order x\<close>
  then have \<open>order x < n\<close> by auto
  then obtain n' where A: \<open>n = order x + n'\<close>
    using less_imp_add_positive by blast
  have B: \<open>n = order x - order y\<close> using order_diff assms by simp
  then have \<open>order x + n' = order x - order y\<close> using A by simp
  then have \<open>n' = 0 - order y\<close> by simp
  then have \<open>order y = 0\<close> using B \<open>order x < n\<close> by linarith
  then have \<open>order x = n\<close> using B by simp
  then show \<open>False\<close> using \<open>order x < n\<close> by simp
qed

lemma \<^marker>\<open>tag (proof) aponly\<close> nth_bearer_order_iff[simp]:  
  assumes \<open>x \<in> \<E>\<close>
  shows \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> #\<beta> x n \<longleftrightarrow> n \<le> order x\<close>
proof (intro iffI inheres_in_by_order[of _ _ \<open>#\<beta> x n\<close>] ; simp?)   
  assume  A: \<open>n \<le> order x\<close>  
  then obtain n' where B: \<open>order x = n + n'\<close> using le_Suc_ex by blast
  have C: \<open>x \<triangleleft>\<triangleleft>\<^bsup>order x\<^esup> !\<beta> x\<close> using assms by blast
  then have D: \<open>x \<triangleleft>\<triangleleft>\<^bsup>n + n'\<^esup> !\<beta> x\<close> using B by simp
  then obtain y where E: \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> y\<close> by (metis relcomppE relpowp_add)
  then  have \<open>#\<beta> x n = y\<close> using nth_bearer_eqI by simp
  then show \<open>x \<triangleleft>\<triangleleft>\<^bsup>n\<^esup> #\<beta> x n\<close> using E by simp
qed

lemma \<^marker>\<open>tag (proof) aponly\<close> substantial_order:
  assumes \<open>x \<in> \<S>\<close> 
  shows \<open>order x = 0\<close>
  using assms \<S>_def 
  by (simp add: order_eq_simp)

lemma \<^marker>\<open>tag (proof) aponly\<close> moment_order_Suc:
  assumes \<open>x \<triangleleft> y\<close>
  shows \<open>order x = Suc (order y)\<close>
proof -
  obtain \<open>x \<in> \<E>\<close> \<open>y \<in> \<E>\<close> 
    using inherence_scope assms by blast  
  then obtain A: \<open>x \<triangleleft>\<triangleleft>\<^bsup>order x\<^esup> !\<beta> x\<close> \<open>y \<triangleleft>\<triangleleft>\<^bsup>order y\<^esup> !\<beta> y\<close> by blast
  then have B: \<open>y \<triangleleft>\<triangleleft>\<^bsup>order y\<^esup> !\<beta> x\<close> 
    using assms ultimate_bearer_eqI1[of x y]     
    by (simp add: tranclp.r_into_trancl)  
  have C: \<open>x \<triangleleft>\<triangleleft>\<^bsup>1\<^esup> y\<close> using assms by auto
  have D: \<open>1 \<le> order x\<close> using C inheres_in_by_order by blast
  have E: \<open>y \<triangleleft>\<triangleleft>\<^bsup>order x - 1\<^esup> !\<beta> x\<close> using inherence_mid_point C A(1) D by metis
  then have \<open>order y = order x - 1\<close> using A(2) B unique_order by blast
  then show \<open>order x = Suc (order y)\<close> using D by linarith
qed

text_raw \<^marker>\<open>tag bodyonly\<close> \<open>\end{itemize}\<close>
text_raw\<open>\par\<close>
end \<^marker>\<open>tag aponly\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  All the axioms regarding the inherence relation in the
  original theory, stated in the @{locale inherence_original} locale, are
  derivable from the basic inherence axioms (@{locale inherence_base} locale)
  plus the noetherian axiom:
\<close>
text_raw\<open>\par\<close>
sublocale 
  noetherian_inherence \<subseteq> inherence_original
proof \<^marker>\<open>tag aponly\<close> (unfold_locales)  
  have acyclic_conv: \<open>acyclicP ((\<triangleleft>)\<inverse>\<inverse>)\<close> 
    using wfP_acyclicP inherence_is_noetherian  by blast
  then have acyclic: \<open>acyclicP (\<triangleleft>)\<close> using acyclicP_converse by auto
  then have inh_acyclic: \<open>\<not> (\<triangleleft>)\<^sup>+\<^sup>+ x x\<close> for x
    by (simp add: Nitpick.tranclp_unfold acyclic_def)  
  then show 
    inh_irrefl: \<open>\<not> x \<triangleleft> x\<close> for x by blast 
  show asym: \<open>\<not> y \<triangleleft> x\<close> if \<open>x \<triangleleft> y\<close> for x y
  proof
    assume \<open>y \<triangleleft> x\<close>
    then obtain \<open>(\<triangleleft>)\<^sup>*\<^sup>* x y\<close> \<open>(\<triangleleft>)\<^sup>*\<^sup>* y x\<close> using \<open>x \<triangleleft> y\<close> by blast
    then have \<open>x = y\<close>
      by (metis acyclic_impl_antisym_rtrancl[to_pred] 
                acyclic antisymD[to_pred])
    then show \<open>False\<close> using inh_irrefl \<open>x \<triangleleft> y\<close> by simp
  qed  
  show \<open>\<not> x \<triangleleft> z\<close> if  A: \<open>x \<triangleleft> y\<close> \<open>y \<triangleleft> z\<close> for x y z
    using A by (meson inherence_antitransitive_V1)
qed

text \<^marker>\<open>tag bodyonly\<close> \<open>
  The axioms of the revised inherence theory @{locale inherence_V2},
  that explicitly excludes cycles from the @{locale inherence_original} theory,
  are also derivable from the noetherian axiom:
\<close>
text_raw\<open>\par\<close>
sublocale noetherian_inherence \<subseteq> inherence_V2
proof \<^marker>\<open>tag aponly\<close> (unfold_locales)
  have acyclic_conv: \<open>acyclicP ((\<triangleleft>)\<inverse>\<inverse>)\<close> 
    using wfP_acyclicP inherence_is_noetherian  by blast
  then have acyclic: \<open>acyclicP (\<triangleleft>)\<close> using acyclicP_converse by auto
  then show \<open>\<not> (\<triangleleft>)\<^sup>+\<^sup>+ x x\<close>  for x
    by (simp add: Nitpick.tranclp_unfold acyclic_def)  
qed

text \<^marker>\<open>tag bodyonly\<close> \<open>
  Furthermore, the axioms of the revised inherence theory @{locale inherence_V3},
  that explicitly excludes infinite ascending inherence chains from the 
  @{locale inherence_V2} theory, are also derivable from the noetherian axiom:
\<close>
text_raw\<open>\par\<close>
sublocale 
  noetherian_inherence \<subseteq> inherence_V3
proof \<^marker>\<open>tag aponly\<close> (unfold_locales)
  have acyclic_conv: \<open>acyclicP ((\<triangleleft>)\<inverse>\<inverse>)\<close> 
    using wfP_acyclicP inherence_is_noetherian by blast
  then have acyclic: \<open>acyclicP (\<triangleleft>)\<close> 
    using acyclicP_converse by auto
  show \<open>\<not> inf_inh_asc_chain X x\<close> for X x 
  proof (auto simp: inf_inh_asc_chain_def)
    assume \<open>\<forall>y. y \<in> X \<longleftrightarrow> (\<triangleleft>)\<^sup>*\<^sup>* x y\<close>
    then have X_eq[simp]: \<open>X = { y . (\<triangleleft>)\<^sup>*\<^sup>* x y }\<close> by blast     
    then have \<open>x \<in> X\<close> by auto
    consider \<open>x \<notin> \<E>\<close> | \<open>x \<in> \<S>\<close> | \<open>x \<in> \<M>\<close> using \<S>_def by auto
    then show \<open>finite X\<close>
    proof (cases)
      assume \<open>x \<notin> \<E>\<close>
      then have \<open>X = {x}\<close> 
        using X_eq inherence_scope
        by (smt Collect_cong Nitpick.rtranclp_unfold 
            empty_iff inherence_base.endurantI1 
            inherence_base.trans_inheres_in_scope 
            inherence_base_axioms insert_compr)
      then show \<open>finite X\<close> by auto
    next
      assume \<open>x \<in> \<S>\<close> 
      then have \<open>\<not> x \<triangleleft> y\<close> for y using \<S>_def \<M>_def by blast
      then have \<open>\<not> (\<triangleleft>)\<^sup>+\<^sup>+ x y\<close> for y by (meson tranclpD)
      then have \<open>y = x\<close> if \<open>(\<triangleleft>)\<^sup>*\<^sup>* x y\<close> for y 
        by (metis Nitpick.rtranclp_unfold that)
      then have \<open>X = {x}\<close> using X_eq by auto
      then show \<open>finite X\<close> by auto
    next
      assume \<open>x \<in> \<M>\<close>                  
      have A1: \<open>\<forall>Q. (\<exists>x. x \<in> Q) \<longrightarrow> (\<exists>z\<in>Q. \<forall>y. (\<triangleleft>)\<^sup>+\<^sup>+ z y \<longrightarrow> y \<notin> Q)\<close>
        using inherence_is_noetherian[THEN wfP_trancl]
        by (simp add: tranclp_converse wf_eq_minimal[to_pred] ; metis)
      have A2: \<open>P\<close> 
        if AA: \<open>t \<in> X\<close> \<open>\<And>z. \<lbrakk>z \<in> X ; \<And>y. (\<triangleleft>)\<^sup>+\<^sup>+ z y \<Longrightarrow> y \<notin> X\<rbrakk> \<Longrightarrow> P\<close> for t P
      proof -
        obtain z where BB: \<open>z \<in> X\<close> \<open>\<forall>y. (\<triangleleft>)\<^sup>+\<^sup>+ z y \<longrightarrow> y \<notin> X\<close>
          using AA A1 by metis
        then show \<open>P\<close> using AA BB by metis
      qed     
      show \<open>finite X\<close>
      proof (rule A2[of \<open>x\<close>,OF \<open>x \<in> X\<close>])      
        fix z
        assume as: \<open>z \<in> X\<close> \<open>\<And>y. (\<triangleleft>)\<^sup>+\<^sup>+ z y \<Longrightarrow> y \<notin> X\<close>              
        then have AA: \<open>(\<triangleleft>)\<^sup>*\<^sup>* x z\<close> using X_eq by auto        
        then obtain n\<^sub>z where nz: \<open>((\<triangleleft>)^^n\<^sub>z) x z\<close> by (meson rtranclp_power)
        then have \<open>z \<in> X\<close> using X_eq as(1) by blast
        have \<open>n \<le> n\<^sub>z\<close> if \<open>((\<triangleleft>)^^n) x y\<close> for y n
        proof (rule ccontr)
          assume \<open>\<not> n \<le> n\<^sub>z\<close>
          then have \<open>n\<^sub>z < n\<close> by simp
          then have \<open>n\<^sub>z \<le> n\<close> by auto
          then have \<open>((\<triangleleft>)^^(n-n\<^sub>z)) z y\<close> 
            using inherence_mid_point \<open>((\<triangleleft>)^^n) x y\<close> nz by blast
          then obtain k where \<open>z \<triangleleft> k\<close> 
            using \<open>n\<^sub>z < n\<close> by (meson \<open>\<not> n \<le> n\<^sub>z\<close> diff_is_0_eq relpowp_E2)
          then have \<open>(\<triangleleft>)\<^sup>+\<^sup>+ z k\<close> by simp
          then have \<open>k \<notin> X\<close> using as(2) by simp
          have \<open>(\<triangleleft>)\<^sup>+\<^sup>+ x k\<close> using \<open>(\<triangleleft>)\<^sup>+\<^sup>+ z k\<close> \<open>((\<triangleleft>)^^n\<^sub>z) x z\<close> AA  by auto
          then have \<open>k \<in> X\<close> using X_eq by simp    
          then show \<open>False\<close> using \<open>k \<notin> X\<close> by simp
        qed
        define Y where \<open>Y = { n . n \<le> n\<^sub>z}\<close>
        have ex_bearer: \<open>\<exists>y. ((\<triangleleft>)^^n) x y\<close> if \<open>n \<in> Y\<close> for n 
        proof -
          have \<open>n\<^sub>z = n + (n\<^sub>z - n)\<close> using that Y_def by simp
          then have \<open>((\<triangleleft>)^^(n + (n\<^sub>z - n))) x z\<close> using nz by simp
          then have \<open>(((\<triangleleft>)^^n) OO ((\<triangleleft>)^^(n\<^sub>z - n))) x z\<close> 
            by (simp add: relpowp_add)
          then obtain t where \<open>((\<triangleleft>)^^n) x t\<close> \<open>((\<triangleleft>)^^(n\<^sub>z - n)) t z\<close> by blast
          then show \<open>?thesis\<close> by metis
        qed
        have ex1_bearer: \<open>\<exists>!y. ((\<triangleleft>)^^n) x y\<close> if \<open>n \<in> Y\<close> for n
          by (auto intro!: ex_bearer that nth_inherence_unique_cond)          
        define F where \<open>F n \<equiv> THE y. ((\<triangleleft>)^^n) x y\<close> for n
        have \<open>F n \<in> X\<close> if \<open>n \<in> Y\<close> for n
        proof -
          have A: \<open>\<exists>!y. ((\<triangleleft>)^^n) x y\<close> using ex1_bearer Y_def that by blast
          then obtain k where B: \<open>((\<triangleleft>)^^n) x k\<close> by blast
          then have F_eq: \<open>F n = k\<close>
            by (simp only: F_def ; metis the1_equality A B)            
          then have \<open>((\<triangleleft>)^^n) x (F n)\<close> using B F_eq by simp
          then show \<open>F n \<in> X\<close> using X_eq rtranclp_power by fastforce
        qed
        have exY: \<open>\<exists>n \<in> Y. F n = y\<close> if \<open>y \<in> X\<close> for y
        proof (simp add: Y_def F_def)
          have \<open>(\<triangleleft>)\<^sup>*\<^sup>* x y\<close> using that X_eq by blast
          then obtain n\<^sub>y where \<open>((\<triangleleft>)^^n\<^sub>y) x y\<close> by (meson rtranclp_imp_relpowp)
          have \<open>n\<^sub>y \<le> n\<^sub>z\<close>
          proof (rule ccontr)
            assume as1: \<open>\<not> n\<^sub>y \<le> n\<^sub>z\<close>
            then have \<open>n\<^sub>z < n\<^sub>y\<close> by simp
            then have \<open>n\<^sub>z \<le> n\<^sub>y\<close> by simp
            then have \<open>((\<triangleleft>)^^(n\<^sub>y-n\<^sub>z)) z y\<close>
              using inherence_mid_point \<open>((\<triangleleft>)^^n\<^sub>y) x y\<close> \<open>((\<triangleleft>)^^n\<^sub>z) x z\<close> 
              by metis
            then obtain k where \<open>z \<triangleleft> k\<close> using \<open>n\<^sub>z < n\<^sub>y\<close> 
              by (meson as1 diff_is_0_eq relpowp_E2)
            then have \<open>(\<triangleleft>)\<^sup>+\<^sup>+  z k\<close> by simp
            then have \<open>k \<notin> X\<close> using as(2) by simp
            have \<open>(\<triangleleft>)\<^sup>*\<^sup>* x k\<close> using \<open>((\<triangleleft>)^^n\<^sub>z) x z\<close> \<open>(\<triangleleft>)\<^sup>+\<^sup>+  z k\<close> AA by auto
            then have \<open>k \<in> X\<close> using X_eq by blast
            then show \<open>False\<close> using \<open>k \<notin> X\<close> by simp
          qed            
          then have \<open>n\<^sub>y \<in> Y\<close> using Y_def by auto
          then have \<open>The (((\<triangleleft>) ^^ n\<^sub>y) x) = y\<close> 
            using \<open>((\<triangleleft>)^^n\<^sub>y) x y\<close>            
            by (simp add: nth_inherence_unique_cond the_equality)
          then show \<open>\<exists>n\<le>n\<^sub>z. The (((\<triangleleft>) ^^ n) x) = y\<close> 
            using \<open>n\<^sub>y \<le> n\<^sub>z\<close> by blast
        qed
        have F_img: \<open>F ` Y = X\<close> using exY \<open>\<And>n. n \<in> Y \<Longrightarrow> F n \<in> X\<close> by blast
        have finite_Y: \<open>finite Y\<close> by (simp add: Y_def)
        show \<open>finite X\<close> using finite_surj finite_Y F_img by blast
      qed
    qed
  qed
qed

lemma \<^marker>\<open>tag aponly\<close> (in inherence_V3) inherence_V3_impl_noetherian_inherence:
  \<open>noetherian_inherence \<W> (\<triangleleft>)\<close>
proof (unfold_locales)
  have \<open>\<not> has_moment_without_ultimate_bearer\<close>
    using no_ultimate_bearer_problem by blast
  then show \<open>wfP (\<triangleleft>)\<inverse>\<inverse>\<close> 
    using no_ultimate_bearer_problem_eq_noetherian by linarith
qed

text \<^marker>\<open>tag bodyonly\<close> \<open>
  In fact, the theory @{locale inherence_V3} is logically equivalent
  to the @{locale noetherian_inherence} theory:
\<close>
text_raw\<open>\par\<close>
lemma inherence_V3_and_noetherian_inherence_are_eq:
  \<open>inherence_V3 \<W> inheresIn \<longleftrightarrow> noetherian_inherence \<W> inheresIn\<close>  
  (is "?G1 \<longleftrightarrow> ?G2")
proof \<^marker>\<open>tag aponly\<close>
  show A: "?G2" if "?G1"    
    using inherence_V3.inherence_V3_impl_noetherian_inherence that by metis
  show B: "?G1" if "?G2"
  proof -
    interpret noetherian_inherence \<W> inheresIn using that by simp
    show "?G1" by (simp add: inherence_V3_axioms)
  qed
qed

locale \<^marker>\<open>tag aponly\<close> inherence = noetherian_inherence +
  assumes inherence_is_wf[intro!,simp]: \<open>wfP (\<triangleleft>)\<close>
begin \<^marker>\<open>tag aponly\<close>

text \<^marker>\<open>tag bodyonly\<close> \<open>
  Since the noetherian axiom 
  \[ @{thm_name inherence_is_notherian} \]
  is equivalent to the axioms of the @{locale inherence_V3} locale minus
  those of of the @{locale inherence_base} locale (
    @{thm_name inherence_original.inherence_irrefl},
    @{thm_name inherence_original.inherence_asymm},
    @{thm_name inherence_original.inherence_antitransitive}, \\
    @{thm_name inherence_V2.no_inherence_cycles} and
    @{thm_name inherence_V3.no_infinite_inherence_chains}),
  we replace these 5 axioms with the former in the inherence
  theory that shall be used in this thesis.

  However, we add a further axiom to further restrict the inherence
  relation in such a way that no infinite descending chains occur.
  
  Such a chain would represent a non-ending causal chain of explanation for
  why a substantial has some property P represented by a certain moment
  \<open>m\<close> that is part of the chain. It is as if no final answer could be given
  as to what grounds the fact that the substantial has the property P:
  it is P because it bears a moment \<open>m\<^sub>1\<close>; \<open>m\<^sub>1\<close> is what it is because it
  bears moment \<open>m\<^sub>2\<close>; \<open>m\<^sub>2\<close> is what it is because it bears moment \<open>m\<^sub>3\<close> and
  so forth.

  To avoid this situation, we require that the inherence relation be not
  only noetherian but also well-founded. The resulting locale, @{locale inherence},
  adds the following axiom to the @{locale noetherian_inherence} locale:

  \begin{axiom}[$@{thm_name inherence_is_wf}$]
    The inherence relation must be well-founded, or, in other words,
    for any non-empty set \<open>Q\<close> of particulars, there must be a member
    \<open>z\<close> of \<open>Q\<close> such that, for any \<open>y\<close>, if \<open>y\<close> inheres in \<open>z\<close> then 
    \<open>y\<close> is not on \<open>Q\<close>:

    \[ @{thm inherence_is_wf}\text{, or} \]
    \[ @{thm inherence_is_wf[simplified wfP_eq_minimal,simplified,rule_format]} \]
  \end{axiom}
 
\<close>
text_raw\<open>\par\<close>
lemmas \<^marker>\<open>tag aponly\<close> just_inherence_axioms = inherence_is_wf

lemmas \<^marker>\<open>tag aponly\<close> all_inherence_axioms =
  all_noetherian_inherence_axioms just_inherence_axioms

lemma \<^marker>\<open>tag (proof) aponly\<close> ultimte_bearer_ed: 
    \<open>ed x (!\<beta> y)\<close> if \<open>ed x y\<close> for x y
    apply (auto simp: ed_def)
    subgoal G1 using that edE by auto
    subgoal G2 by (rule edE[OF that] ; simp add: endurantI3)
    subgoal G3 for w
      apply (rule edE[OF that])
      subgoal premises P
        supply R1 = P(5)[OF P(1,2)]
        using R1 P(1,4) 
        apply (induct y rule: wfP_induct[
                OF inherence_is_noetherian] 
              ; simp)
        subgoal premises Q for z          
          using  Q(3) 
          apply (cases z rule: endurant_cases ; (elim \<M>_E)?)
          subgoal G3_1 
            using Q(2) Q(5) 
            by (metis Q(3) rtranclp.rtrancl_refl ultimate_bearer_eq_simp)
          subgoal G3_2 premises T for t
            apply (rule edE[OF inherence_imp_ed[OF T(2)]])
            subgoal premises V                
              supply R2 = V(3)[OF \<open>w \<in> \<W>\<close> \<open>z \<in> w\<close>]
              supply R3 = inherence_imp_ed[OF T(2)]
              supply R4 = ed_scope[OF R3] edD[OF R3]
              supply R5 = 
                Q(1)[rule_format, OF T(2) R2 R4(2)] 
                \<open>z \<triangleleft> t\<close> \<open>z \<in> \<E>\<close> \<open>t \<in> \<E>\<close> \<open>z \<in> w\<close> \<open>t \<in> w\<close> \<open>w \<in> \<W>\<close>
              supply R6 = 
                ultimate_bearer_eq_simp[
                  of z \<open>!\<beta> t\<close>, THEN iffD2, OF _ conjI, symmetric,
                  THEN subst, of \<open>\<lambda>x. x \<in> w\<close>]
              apply (rule R6)
              subgoal G3_2_1 by (simp add: V(1))
              subgoal G3_2_2 
                using ultimate_bearer_is_not_a_moment by (simp add: V(2))
              subgoal G3_2_3
                using R5(2) ultimate_bearer_eqI1 ultimate_bearer_eq_simp 
                by blast
              using R5(1) by simp 
            done
          done
        done
      done
    done

lemma \<^marker>\<open>tag (proof) aponly\<close> ultimate_beaer_idemp[simp]: 
  assumes \<open>x \<in> \<E>\<close>
  shows \<open>!\<beta> (!\<beta> x) = !\<beta> x\<close>
  using assms     
  by (metis rtranclpD ultimate_bearer_eqI1 ultimate_bearer_eq_simp)

text \<^marker>\<open>tag bodyonly\<close> \<open>
  The consequence of the inherence relation being both well-founded and
  noetherian is that all of its inherence chains are finite: \<close>
text_raw\<open>\par\<close>

lemma inherence_chains_are_finite:
  assumes A: \<open>X \<subseteq> \<E>\<close> \<open>X \<noteq> \<emptyset>\<close> 
             \<open>\<And>x y. \<lbrakk> x \<in> X ; y \<in> X \<rbrakk> \<Longrightarrow> x \<triangleleft>\<triangleleft> y \<or> y \<triangleleft>\<triangleleft> x \<or> x = y\<close>
  shows \<open>finite X\<close>
proof \<^marker>\<open>tag aponly\<close> - 
  have B: \<open>inj_on order X\<close>
  proof (intro inj_onI)
    fix x y
    assume AA: \<open>x \<in> X\<close> \<open>y \<in> X\<close> \<open>order x = order y\<close> 
    { assume \<open>x \<noteq> y\<close>
      then consider (c1) \<open>x \<triangleleft>\<triangleleft> y\<close> | (c2) \<open>y \<triangleleft>\<triangleleft> x\<close>
        using A(3) AA(1,2) by metis
      then have False
      proof (cases)
        case c1 then have \<open>order x < order y\<close> by (metis AA(3) order_le)
        then show ?thesis using AA by simp
      next
        case c2 then have \<open>order x < order y\<close> by (metis AA(3) order_le)
        then show ?thesis using AA by simp
      qed }
    then show \<open>x = y\<close> by blast 
  qed
  obtain a 
    where Ca: \<open>a \<in> X\<close> \<open>\<And>y. y \<triangleleft>\<triangleleft> a \<Longrightarrow> y \<notin> X\<close>
    using A(2) inherence_is_wf wfP_eq_minimal    
    by (metis equals0I wfP_trancl)

  obtain b 
    where Cb: \<open>b \<in> X\<close> \<open>\<And>y. b \<triangleleft>\<triangleleft> y \<Longrightarrow> y \<notin> X\<close>
    using A(2) inherence_is_noetherian wfP_eq_minimal            
    by (metis conversep.intros empty_subsetI 
            subset_antisym subset_iff tranclp_converseI wfP_trancl)

  have D: \<open>(\<triangleleft>)\<^sup>*\<^sup>* a x\<close> \<open>(\<triangleleft>)\<^sup>*\<^sup>* x b\<close> if \<open>x \<in> X\<close> for x        
    subgoal by (metis rtranclp.rtrancl_refl tranclp_into_rtranclp that A(3) Ca)     
    by (metis A(3) Cb(1) Cb(2) Nitpick.rtranclp_unfold that)
  then have E: \<open>order b \<le> order x\<close> \<open>order x \<le> order a\<close> if \<open>x \<in> X\<close> for x
    using \<open>x \<in> X\<close> order_le1 by metis+
  define Q :: \<open>nat set\<close> where \<open>Q = { n . order b \<le> n \<and> n \<le> order a }\<close>
  have \<open>finite Q\<close> using Q_def by auto  
  have F: \<open>order ` X \<subseteq> Q\<close> by (auto simp: Q_def intro!: E)
  have \<open>finite (order ` X)\<close> using \<open>finite Q\<close> finite_subset[OF F] by simp    
  then show \<open>finite X\<close> using B finite_imageD by blast
qed

end

end