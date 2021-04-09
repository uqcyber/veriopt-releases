theory Stuttering
  imports
    Semantics.IRStepObj
begin

inductive stutter:: "IRGraph \<Rightarrow> MapState \<Rightarrow> FieldRefHeap \<Rightarrow> ID \<Rightarrow> ID \<Rightarrow> bool" ("_ _ _ \<turnstile> _ \<leadsto> _" 55)
  for g m h where

  StutterStep:
  "\<lbrakk>g \<turnstile> (nid,m,h) \<rightarrow> (nid',m,h)\<rbrakk>
   \<Longrightarrow> g m h \<turnstile> nid \<leadsto> nid'" |

  Transitive:
  "\<lbrakk>g \<turnstile> (nid,m,h) \<rightarrow> (nid'',m,h);
    g m h \<turnstile> nid'' \<leadsto> nid'\<rbrakk>
   \<Longrightarrow> g m h \<turnstile> nid \<leadsto> nid'"

end