
use "chktable.sml";

exception typifyErr
exception checkErr
exception chkelabErr
exception chktypeErr
exception chkelabErr

fun validate (PROG (id, block)) =  
let val emptyenv = emptyEnv() 
    val env = chkextendEnv(emptyenv,id,program)
   in (examine block env) end

and examine (BLOCK (DECLLST decls, CMDLST cmds)) env = 
                       let  val locenv = emptyEnv()
                            val (locenv1, env1) = (chkelabs decls (locenv, env))
                                        in (checks cmds env1)
                                        end

and chkelabs (nil) (locenv, env) = (locenv, env)
   | chkelabs (decl::lst) (locenv, env) = 
      let val (locenv1,env1) = (chkelab decl (locenv,env)) in (chkelabs lst (locenv1,env1)) end

and chkvardecl (id,tp) (locenv,env) = 
   if chkapplyEnv(locenv,id) = unbound then 
   (chkextendEnv(locenv,id, (chktype(tp))),chkextendnEnv(env,id, (chktype(tp))))
   else (print "variable type Error!\n";raise chkelabErr)
   
and chkelab (decl) (locenv,env)  =
   case decl of 
      DECL (tp,id::lst)  =>
                           let val (locenv, env) = (chkvardecl (id,tp) (locenv,env))
                               val dlst = DECL(tp,lst)
                           in (chkelab dlst (locenv,env))
                           end
      |DECL (tp,nil)  => (locenv,env)
      |CONDECL (cons,exp) => 
                         if chkapplyEnv(locenv,cons) = unbound then   (* chkapplyEnv) *)
                         (chkextendEnv(locenv,cons, (typify exp env)),chkextendnEnv(env,cons,(typify exp env)))
                         else (print "const type Error!\n";raise chkelabErr)
                         (*
      |PROC (id,block)  => validate(PROG(id,block))
      |PROCPAR (id,parl,block)  => (locenv,env)
      *)
      |_  => (print "Impossible!\n";raise chkelabErr)

and checks (nil) env = true
| checks (cmd::lst) env = let val b1 = (check cmd env)
                              val b2 = (checks lst env)
                          in (b1 andalso b2)
                          end

and check cmd env =
case cmd of
    ASTSKIP => true
   |ASGN (ide, exp) => let val b1 = (chkapplyEnv(env,ide)=intvar andalso (typify exp env) = intval) 
                             val b2 = ((chkapplyEnv(env,ide) = boolvar andalso (typify exp env) = boolval))
                         in (b1 orelse b2)
                         end
   |ASTWHILE ( exp, cmds ) =>  ((typify exp env) = boolval andalso (checks cmds
   env))
   |CALL ( id ) =>  (chkapplyEnv(env,id)=program)
   |CALLPAR ( id,explst ) =>  let val ret = (exams explst env)
                                in  ((ret=true) andalso (chkapplyEnv(env,id)=program))
                              end
   | ASTIF2 ( exp, cmds ) => ((typify exp env) = boolval andalso (checks cmds env))
   | ASTIF1 ( exp, cmdst, cmdsf )  => ((typify exp env) = boolval andalso
   (checks cmdst env) andalso (checks cmdsf env))
   | ASTDECLB block => (examine block env)
   | ASTREAD ( ide ) => (chkapplyEnv(env,ide) = intvar) orelse (chkapplyEnv(env,ide) = boolvar)
   | ASTWRITE ( exp ) => ((typify exp env) <>unbound)
   |_ =>(raise checkErr)

and exams nil env = true
   | exams (exp::lst) env =
       let val ret = (exams lst env)
       in ((typify exp env)<>unbound) andalso (ret=true)
       end

and typify exp env =
case exp of
    ASTNUM  ( p ) =>  intval
   | ASTBOOL  ( p ) =>  boolval
   | ASTID (p) => (
               case (chkapplyEnv(env,p)) of
                    intvar => intval
                  |boolvar => boolval
                  | intval => intval
                  | boolval => boolval
                  |program => program
                  |unbound => (print "Variable Unbound!\n";raise typifyErr)
                  )

   | ASTNOT (l) => 
              if ((typify l env) = boolval) then boolval
              else (print "Type doesn't match\n"; raise typifyErr)
   | ASTNEG (l) => 
              if ((typify l env) = intval) then intval
              else (print "Type doesn't match\n"; raise typifyErr)
   | ASTPLUS (l, r) => 
              if ((typify l env) = intval) andalso ((typify r env) = intval) then
                intval
              else (print "Type doesn't match\n"; raise typifyErr)
   | ASTMINUS (l, r) => 
              if ((typify l env) = intval) andalso ((typify r env) = intval) then
                intval
              else (print "Type doesn't match\n"; raise typifyErr)
   | ASTTIMES (l, r) => 
              if ((typify l env) = intval) andalso ((typify r env) = intval) then
                intval
              else (print "Type doesn't match\n"; raise typifyErr)
   | ASTDIV (l, r) => 
              if ((typify l env) = intval) andalso ((typify r env) = intval) then
                intval
              else (print "Type doesn't match\n"; raise typifyErr)
   | ASTAND (l, r) => 
              if ((typify l env) = boolval) andalso ((typify r env) = boolval) then
                boolval
              else (print "Type doesn't match\n"; raise typifyErr)
   | ASTOR (l, r) => 
              if ((typify l env) = boolval) andalso ((typify r env) = boolval) then
                boolval
              else (print "Type doesn't match\n"; raise typifyErr)
   | ASTLESS (l, r) => 
              if ((typify l env) = intval) andalso ((typify r env) = intval) then
                boolval
              else (print "Type doesn't match\n"; raise typifyErr)
   | ASTLESSEQ (l, r) => 
              if ((typify l env) = intval) andalso ((typify r env) = intval) then
                boolval
              else (print "Type doesn't match\n"; raise typifyErr)
   | ASTGRTR (l, r) => 
              if ((typify l env) = intval) andalso ((typify r env) = intval) then
                boolval
              else (print "Type doesn't match\n"; raise typifyErr)
   | ASTGRTREQ (l, r) => 
              if ((typify l env) = intval) andalso ((typify r env) = intval) then
                boolval
              else (print "Type doesn't match\n"; raise typifyErr)
   | ASTEQ (l, r) => 
              if ((typify l env) = intval) andalso ((typify r env) = intval)
              orelse (((typify l env) = boolval) andalso (typify r env =
              boolval)) then
                boolval
              else (print "Type doesn't match\n"; raise typifyErr)
   | ASTNEQ (l, r) => 
              if ((typify l env) = intval) andalso ((typify r env) = intval)
              orelse (((typify l env) = boolval) andalso (typify r env = boolval)) then
                boolval
              else (print "Type doesn't match\n"; raise typifyErr)
     | ASTPAREN ( l )  =>  
              if ((typify l env) = boolval) then boolval
              else if ((typify l env) = intval) then intval
                  else  (print "Type doesn't match\n"; raise typifyErr)

val inf = TextIO.openIn "1.pelican";
val lexer = makeLexer( fn n => valOf(inputLine( inf ) ));
fun mklst (END) = END::nil | mklst (v) = v::mklst(lexer());

val tklst = mklst(lexer());
val partr = parse_program(tklst); 
val chk = validate(partr);
