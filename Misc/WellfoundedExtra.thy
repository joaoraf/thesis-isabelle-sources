theory WellfoundedExtra
  imports Main
begin

lemma wfP_inj_wfP:
  fixes R :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> and f :: \<open>'a \<Rightarrow> 'b\<close>
  assumes \<open>wfP R\<close> \<open>inj_on f { x . \<exists>y. R x y \<or> R y x }\<close>
  shows \<open>wfP (\<lambda>x y. \<exists>x\<^sub>1 y\<^sub>1. R x\<^sub>1 y\<^sub>1 \<and> x = f x\<^sub>1 \<and> y = f y\<^sub>1)\<close>
proof -
  define X where \<open>X \<equiv> { x . \<exists>y. R x y \<or> R y x }\<close>
  define X' where \<open>X' \<equiv> f ` X\<close>
  define P where \<open>P \<equiv> \<lambda>x y. \<exists>x\<^sub>1 y\<^sub>1. R x\<^sub>1 y\<^sub>1 \<and> x = f x\<^sub>1 \<and> y = f y\<^sub>1\<close>
  define g where \<open>g \<equiv> inv_into X f\<close>
  have f_inj: \<open>inj_on f X\<close>
    using assms(2) by (auto simp: X_def)
  then have f1: \<open>x = y\<close> if \<open>x \<in> X\<close> \<open>y \<in> X\<close> \<open>f x = f y\<close>  for x y
    using that inj_onD by metis
  have g_inj: \<open>inj_on g X'\<close>
    apply (auto simp: g_def X'_def)
    using f_inj by (simp add: inj_on_def)
  then have g1: \<open>x = y\<close> if \<open>x \<in> X'\<close> \<open>y \<in> X'\<close> \<open>g x = g y\<close>  for x y 
    using that inj_onD by metis
  have gf[simp]: \<open>g (f x) = x\<close> if \<open>x \<in> X\<close> for x 
    using that f_inj by (auto simp: g_def)
  have fg[simp]: \<open>f (g x) = x\<close> if \<open>x \<in> X'\<close> for x
    using that f_inj X'_def by (auto simp: g_def)
  have fg_img[simp]: \<open>f ` g ` Y = Y\<close> if \<open>Y \<subseteq> X'\<close> for Y
    using that apply (auto intro!: that simp: image_def)
    subgoal premises P for x
      apply (intro exI[of _ \<open>g x\<close>] conjI bexI[of _ \<open>x\<close>])
      using P fg by auto
    done      
  have P1: \<open>P x y \<Longrightarrow> x \<in> X' \<and> y \<in> X'\<close> for x y
    by (auto simp: X_def X'_def P_def)
  have \<open>\<exists>z. z \<in> Q \<and> (\<forall>y. R y z \<longrightarrow> y \<notin> Q)\<close> if as: \<open>Q \<noteq> {}\<close> for Q
  proof -
    have AA: \<open>\<exists>x. x \<in> Q\<close> using as by blast
    note assms(1)[simplified wf_eq_minimal[to_pred],simplified,rule_format,OF AA]
    then show \<open>\<exists>z. z \<in> Q \<and> (\<forall>y. R y z \<longrightarrow> y \<notin> Q)\<close>
      by blast 
  qed
  then obtain pick where  
        pick: \<open>\<And>Q. Q \<noteq> {} \<Longrightarrow> pick Q \<in> Q\<close>
              \<open>\<And>Q y. \<lbrakk> Q \<noteq> {} ; R y (pick Q) \<rbrakk> \<Longrightarrow> y \<notin> Q\<close>     
    by moura   
  show \<open>?thesis\<close>
  proof (clarsimp simp add: wf_eq_minimal[to_pred])
    fix Q and x :: \<open>'b\<close>
    assume as: \<open>x \<in> Q\<close>
    define Q' where Q1: \<open>Q' \<equiv> g ` Q\<close>
    define z where \<open>z \<equiv> if Q \<inter> X' \<noteq> {} then f (pick (g ` (Q \<inter> X'))) else x\<close>
    have \<open>Q \<inter> X' \<subseteq> X'\<close> by blast
    then have fgQX'[simp]: \<open>f ` g ` (Q \<inter> X') = Q \<inter> X'\<close> by simp
    show \<open>\<exists>z\<in>Q. \<forall>y. (\<exists>x\<^sub>1 y\<^sub>1. R x\<^sub>1 y\<^sub>1 \<and> y = f x\<^sub>1 \<and> z = f y\<^sub>1) \<longrightarrow> y \<notin> Q\<close>    
    proof (intro bexI[of _ \<open>z\<close>] allI impI ; (elim exE conjE)?) 
      show \<open>z \<in> Q\<close>
      proof (cases \<open>g ` (Q \<inter> X') = {}\<close>)
        assume as1: \<open>g ` (Q \<inter> X') = {}\<close>
        then have \<open>Q \<inter> X' = {}\<close> by auto
        then have \<open>z = x\<close> by (auto simp: z_def)
        then show \<open>z \<in> Q\<close> using as by simp
      next
        assume as1: \<open>g ` (Q \<inter> X') \<noteq> {}\<close>
        then have \<open>Q \<inter> X' \<noteq> {}\<close> by auto
        then have z: \<open>z = f (pick (g ` (Q \<inter> X')))\<close> by (auto simp: z_def)
        have \<open>pick (g ` (Q \<inter> X')) \<in> g ` (Q \<inter> X')\<close> 
          using pick[of \<open>g ` (Q \<inter> X')\<close>] as1 by blast
        then have \<open>f (pick (g ` (Q \<inter> X'))) \<in> Q\<close>
          by (auto simp: z_def)
        then show \<open>z \<in> Q\<close> using z by simp
      qed
      fix y x\<^sub>1 y\<^sub>1
      assume as1: \<open>R x\<^sub>1 y\<^sub>1\<close> \<open>y = f x\<^sub>1\<close> \<open>z = f y\<^sub>1\<close>
      then have x1y1: \<open>x\<^sub>1 \<in> X\<close> \<open>y\<^sub>1 \<in> X\<close> using X_def by auto
      then have yz: \<open>y \<in> X'\<close> \<open>z \<in> X'\<close> using X'_def as1 by auto
      show \<open>y \<notin> Q\<close>
      proof
        assume as2: \<open>y \<in> Q\<close>
        then have QX': \<open>Q \<inter> X' \<noteq> {}\<close> using yz by blast
        then have z: \<open>z = f (pick (g ` (Q \<inter> X')))\<close> using z_def by auto
        have gQX'_ss: \<open>g ` (Q \<inter> X') \<subseteq> X\<close> using X'_def by auto
        have \<open>g ` (Q \<inter> X') \<noteq> {}\<close> using QX' by blast
        then obtain pick1: \<open>pick (g ` (Q \<inter> X')) \<in> g ` (Q \<inter> X')\<close>
            \<open>\<And>y. R y (pick (g ` (Q \<inter> X'))) \<Longrightarrow> y \<notin> g ` (Q \<inter> X')\<close>
          using pick by metis
        then have \<open>pick (g ` (Q \<inter> X')) \<in> X\<close> using gQX'_ss by blast
        then have \<open>y\<^sub>1 = pick (g ` (Q \<inter> X'))\<close> 
          using f1  x1y1(2) z as1(3) by metis
        then have pick2: \<open>\<And>y. R y y\<^sub>1 \<Longrightarrow> y \<notin> g ` (Q \<inter> X')\<close>
          using pick1(2) by auto
        then have \<open>x\<^sub>1 \<notin> g ` (Q \<inter> X')\<close> using as1(1) by metis
        then show \<open>False\<close>           
          by (metis IntI as1(2) as2 gf imageI x1y1(1) yz(1))           
      qed        
    qed
  qed
qed
    
  



end


