open TextIO;
use "../wren.lex.sml";

open WrenLex;
open Array;
open UserDeclarations;

Control.Print.printDepth := 100;
Control.Print.printLength := 100;

datatype asttype = ASTTP of string
datatype astidlist = ASTIDL of string list
datatype astexp = ASTNUM of int | ASTID of string | ASTBOOL of bool | ASTAND of (astexp * astexp) 
                | ASTPLUS of (astexp * astexp) | ASTMINUS of (astexp * astexp)
                | ASTTIMES of (astexp * astexp) |ASTDIV of (astexp * astexp)
                | ASTOR of (astexp * astexp) | ASTLESSEQ of (astexp * astexp) 
                | ASTLESS of (astexp * astexp) | ASTEQ of (astexp *astexp) 
                | ASTGRTR of (astexp * astexp) | ASTGRTREQ of (astexp * astexp) | ASTNEQ of (astexp * astexp) 
                | ASTNEG of astexp | ASTNOT of astexp |ASTPAREN of astexp
datatype astcmd = ASGN of (string * astexp) | ASTSKIP | EMPTY
                | ASTREAD of string | ASTWRITE of astexp 
                | ASTWHILE of ( astexp * astcmd list) | ASTIF1 of ( astexp *
                astcmd list* astcmd list) |ASTIF2 of (astexp * astcmd list) 
                | ASTLABEL of (string * astcmd list) | ASTGOTO of string
                | ASTSTOP 
datatype astcmds =  CMDLST of astcmd list
datatype ast =  PROG of astcmds

fun printlist(nil) = print ""
    |printlist(t)=( print(hd(t));print(" ");printlist(tl(t))
      );

fun parTKL ([END]) = ["END "]
  | parTKL (nil) = ["END\n"]
  | parTKL (lst) =
  case lst of
      DIV ::tr =>  "DIV "::parTKL(tr)
     | READ ::tr => "READ "::parTKL(tr) 
     | WRITE ::tr => "WRITE " :: parTKL(tr) 
     | TYPE tp ::tr => "TYPE " :: parTKL(tr) 
     | EOF ::tr =>  "EOF "::parTKL(tr)
     | EOS ::tr =>  "EOS "::parTKL(tr)
     | ID ide ::tr =>  "ID "::parTKL(tr)
     | NUM nm ::tr =>  "NUM "::parTKL(tr)
     | BOOL bl ::tr =>  "BOOL "::parTKL(tr)
     | PLUS ::tr =>  "PLUS "::parTKL(tr)
     | MINUS ::tr =>  "MINUS "::parTKL(tr)
     | TIMES ::tr =>  "TIMES "::parTKL(tr)
     | PRINT ::tr =>  "PRINT "::parTKL(tr)
     | LPAREN ::tr =>  "LPAREN "::parTKL(tr)
     | RPAREN ::tr =>  "RPAREN "::parTKL(tr)
     | LESS ::tr =>  "LESS "::parTKL(tr)
     | LESSEQ ::tr =>  "LESSEQ "::parTKL(tr)
     | GRTR ::tr =>  "GRTR "::parTKL(tr)
     | GRTREQ ::tr =>  "GRTREQ "::parTKL(tr)
     | EQ ::tr =>  "EQ "::parTKL(tr)
     | NEQ ::tr =>  "NEQ "::parTKL(tr)
     | AND ::tr =>  "AND "::parTKL(tr)
     | NOT ::tr =>  "NOT "::parTKL(tr)
     | OR ::tr =>  "OR "::parTKL(tr)
     | PROGRAM ::tr =>  "PROGRAM "::parTKL(tr)
     | COLON ::tr =>  "COLON "::parTKL(tr)
     | COMMA ::tr =>  "COMMA "::parTKL(tr)
     | ASSIGN ::tr =>  "ASSIGN "::parTKL(tr)
     | VAR ::tr =>  "VAR "::parTKL(tr)
     | BEGIN ::tr =>  "BEGIN "::parTKL(tr)
     | WHILE ::tr =>  "WHILE "::parTKL(tr)
     | DO ::tr =>  "DO "::parTKL(tr)
     | SKIP ::tr =>  "SKIP "::parTKL(tr)
     | ENDWHILE ::tr =>  "ENDWHILE "::parTKL(tr)
     | ENDIF ::tr =>  "ENDIF "::parTKL(tr)
     | IS ::tr => "IS "::parTKL(tr) 
     | END ::tr => "END "::parTKL(tr) 
     | _  => ["uncatchced "]

exception progErr
exception blkErr
exception declErr
exception declsErr
exception cmdErr
exception cmdsErr
exception expErr
exception asgnErr
exception whileErr
exception ifErr
exception idlErr
exception factErr
exception oprtErr
exception logicErr
exception rltnlErr
exception prodErr
exception lfprodErr

fun parse_fact (nil) = (print "Expect Factor!\n"; raise factErr)
  | parse_fact (lst) =
  case lst of
       NUM nm ::tr =>(ASTNUM(nm),tr)
     | ID ide ::tr  => (ASTID(ide),tr)
     | BOOL bl ::tr  => (ASTBOOL(bl),tr)
     | LPAREN :: tr => let val (rf, ts) = parse_fact(tr)
                                  val (r, tc) = parse_oprt(rf,ts)
                         in case tc of
                                 RPAREN :: ts => (ASTPAREN(r),ts)
                               | _ => (print "expect right paren!\n"; raise
                               expErr)
                       end
     | NOT :: LPAREN :: tr => let val (rf, ts) = parse_fact(tr)
                                  val (r, tc) = parse_oprt(rf,ts)
                         in case tc of
                                 RPAREN :: ts => (ASTNOT(r),ts)
                               | _ => (print "expect right paren!\n"; raise
                               expErr)
                         end
  | MINUS :: tr => let val (r, tc) = parse_fact(tr) 
                 in (ASTNEG(r),tc) 
                 end
  | _ =>  (print " expect terminal term!\n"; raise expErr)                                                           

  and parse_lfprod (nil) = (print " Error in LFPROD\n";raise lfprodErr)
    | parse_lfprod (lst) =
  case lst of
       TIMES::tr => true
     | DIV::tr => true
     | _   => false

  and parse_prod (r1, lst) =
  case lst of
       TIMES ::tr => let val (r2,ts) = parse_fact(tr)
                     in parse_prod(ASTTIMES(r1,r2),ts)
                     end
     |DIV ::tr => let val (r2,ts) = parse_fact(tr)
                     in parse_prod(ASTDIV(r1,r2),ts)
                  end
     |_   => (r1,lst)

  and  parse_arthm (r1,lst) =
   case lst of
        PLUS::tr => let val (r2,ts) = parse_fact(tr)
                        val k = parse_lfprod(ts)
                    in case k of
                            true => let val (r3,tc) = parse_prod(r2,ts)
                                    in parse_arthm(ASTPLUS(r1,r3),tc)
                                    end
                          | false => parse_arthm(ASTPLUS(r1,r2),ts)
                    end
      | MINUS::tr => let val (r2,ts) = parse_fact(tr)
                        val k = parse_lfprod(ts)
                    in case k of
                            true => let val (r3,tc) = parse_prod(r2,ts)
                                    in parse_arthm(ASTMINUS(r1,r3),tc)
                                    end
                          | false => parse_arthm(ASTMINUS(r1,r2),ts)
                    end
      | TIMES::tr => parse_prod(r1,lst)
                      
      | DIV::tr => parse_prod(r1,lst)
      | _ => (r1,lst)

  and  parse_rltnl (r1,lst) =
   case lst of 
        LESS :: tr => 
                   let val (rf,ts) = parse_fact(tr)
                   val (r2,tc) = parse_arthm(rf,ts)
                   in parse_rltnl(ASTLESS(r1,r2),tc)
                   end
      | LESSEQ :: tr =>
                   let val (rf,ts) = parse_fact(tr)
                   val (r2,tc) = parse_arthm(rf,ts)
                   in parse_rltnl(ASTLESSEQ(r1,r2),tc)
                   end
      | EQ :: tr =>
                   let val (rf,ts) = parse_fact(tr)
                   val (r2,tc) = parse_arthm(rf,ts)
                   in parse_rltnl(ASTEQ(r1,r2),tc)
                   end
      | NEQ :: tr =>
                   let val (rf,ts) = parse_fact(tr)
                   val (r2,tc) = parse_arthm(rf,ts)
                   in parse_rltnl(ASTNEQ(r1,r2),tc)
                   end
      | GRTR :: tr =>
                   let val (rf,ts) = parse_fact(tr)
                   val (r2,tc) = parse_arthm(rf,ts)
                   in parse_rltnl(ASTGRTR(r1,r2),tc)
                   end
      | GRTREQ :: tr =>
                   let val (rf,ts) = parse_fact(tr)
                   val (r2,tc) = parse_arthm(rf,ts)
                   in parse_rltnl(ASTGRTREQ(r1,r2),tc)
                   end
      | _ => parse_arthm(r1,lst)


  and parse_logic (r1,lst) =
   case lst of
        AND::tr => 
                   let val (rf,ts) = parse_fact(tr)
                   val (r2,tc) = parse_rltnl(rf,ts)
                   val itm = ASTAND(r1,r2)
                   in parse_logic(itm,tc)
                   end
      | OR::tr =>  
                   let val (rf,ts) = parse_fact(tr)
                   val (r2,tc) = parse_rltnl(rf,ts)
                   in parse_logic(ASTOR(r1,r2),tc)
                   end
      | _ => 
            parse_rltnl(r1,lst)
                   


  and parse_oprt (r1,lst) =
   case lst of
        PLUS::tr => let val (itm,ts) = parse_arthm(r1,lst)
                    in parse_oprt(itm,ts)
                    end
      | MINUS::tr => let val (itm,ts) = parse_arthm(r1,lst)
                    in parse_oprt(itm,ts)
                    end
      | TIMES::tr => let val (itm,ts) = parse_arthm(r1,lst)
                    in parse_oprt(itm,ts)
                    end
      | DIV::tr => let val (itm,ts) = parse_arthm(r1,lst)
                    in parse_oprt(itm,ts)
                    end
      | LESS::tr => let val (itm,ts) = parse_rltnl(r1,lst)
                    in parse_oprt(itm,ts)
                    end
      | LESSEQ::tr => let val (itm,ts) = parse_rltnl(r1,lst)
                    in parse_oprt(itm,ts)
                    end
      | EQ::tr => let val (itm,ts) = parse_rltnl(r1,lst)
                    in parse_oprt(itm,ts)
                    end
      | NEQ::tr => let val (itm,ts) = parse_rltnl(r1,lst)
                    in parse_oprt(itm,ts)
                    end
      | GRTR::tr => let val (itm,ts) = parse_rltnl(r1,lst)
                    in parse_oprt(itm,ts)
                    end
      | GRTREQ::tr => let val (itm,ts) = parse_rltnl(r1,lst)
                    in parse_oprt(itm,ts)
                    end
      | AND::tr => let val (itm,ts) = parse_logic(r1,lst)
                    in parse_oprt(itm,ts)
                    end
      | OR::tr => let val (itm,ts) = parse_logic(r1,lst)
                    in parse_oprt(itm,ts)
                    end
      | RPAREN::tr =>(r1,lst)
      | _ => (r1,lst)


  and parse_exp (nil) = (print "incomplete input\n";raise expErr)
   | parse_exp (lst) =
   let val (r,tr) = parse_fact(lst)
       val (r1,tc) = parse_oprt(r,tr)
   in (r1,tc) 
   end


  and parse_while (nil) = (print "Expect WHILE BODY!\n";raise whileErr)
  | parse_while (lst) =
  case lst of 
       WHILE :: tr => let val (exp,DO::tc) = parse_exp(tr)
                          val (cmds, tc1) = parse_cmds(tc)
                       in case tc1 of
                               ENDWHILE::EOS::tc2  =>(ASTWHILE(exp,cmds),tc2)
                               
                              | _ => (print ("Expect ENDWHILE and SEMICOLON!\n"); raise(whileErr))
                      end
      | _ => (print ("Expect While!\n"); raise(whileErr))
                                
  and parse_if (nil) = (print "Expect IF BODY!\n"; raise ifErr)
  | parse_if (lst) =
  case lst of 
       IF :: tr => let val (exp, THEN::tc) = parse_exp(tr);
                       val (cmd, tc1) = parse_cmds(tc)
                   in case tc1 of
                           ELSE::tc2 => let val(cmd2,tr1) = parse_cmds(tc2)
                                        in case tr1 of
                                        ENDIF::EOS::tr2 => (ASTIF1(exp,cmd,cmd2),tr2) 
                                       | ENDIF::tr2 => (print ("Expect SEMICOLON!\n");raise(ifErr))
                                       | _ => (print ("Expect ENDIF and SEMICOLON!\n");raise(ifErr))
                                        end
                           | ENDIF::EOS::tc2 => (ASTIF2(exp,cmd),tc2)
                           | _ => (print ("Expect ELSE or ENDIF and SEMICOLON!\n");raise(ifErr))
                   end
     | _ => (print ("Expect If!\n");raise(ifErr))

  and parse_asgn (nil) = (print "Expect ASSIGNMENT BODY!\n"; raise asgnErr)
  | parse_asgn (lst) =
  case lst of
       ID ide :: ASSIGN :: tr => let val (exp, tr1) = parse_exp(tr)
                                 in case tr1 of
                                 EOS:: tr2 => let val asn = ASGN(ide,exp)
                                              in (asn,tr2) 
                                              end
                                            (*  (ASGN(ASTID(ide), exp),tr2) *)
                                | ENDWHILE::tr2 => (ASGN(ide,exp),tr1)
                                | _ => (print ("Expect SEMICOLON OR ENDWHILE \n");raise(asgnErr))
                                 end
     | _ => (print ("Expect ID!\n");raise(asgnErr))

  
  and parse_cmd (nil) = (print "Expect COMMAND BODY!\n";raise cmdErr)
  | parse_cmd (lst) =
  case lst of 
      ID id :: COLON::tr => (print "Here is label\n";  (ASTLABEL(id,nil),tr))
     | ID ide::ASSIGN::tr => parse_asgn(lst)
     | WHILE ::tr => parse_while(lst)
     | IF :: tr=> parse_if(lst)
     | READ :: tr=> (
                    case tr of
                    ID ide :: tc => (ASTREAD(ide),tc) 
                       | _ => ( print "Expect ID for reading!";raise cmdErr) )
     | WRITE :: tr=> 
         let val (exp, tc) = parse_exp(tr)
         in (ASTWRITE(exp),tc)
         end
     | SKIP :: tr => (ASTSKIP, tr) 
     | GOTO::ID ide :: tr => (ASTGOTO(ide), tr) 
     | _ => (printlist(parTKL(lst));print "\nNot a beginning keyword of a COMMAND!\n"; raise cmdErr)

  and parse_cmds (nil) = (print "Expect COMMAND BODY!\n";raise cmdsErr)
  | parse_cmds (lst) =
  case lst of 
       [END] => (nil,lst)
     | ENDWHILE :: tr => (nil,lst)
     | ENDIF :: tr => (nil,lst)
     | ELSE :: tr => (nil,lst)
     | _ => let val (r, ts) = parse_cmd(lst)
             val (rd,tr) = parse_cmds(ts)
            in (r::rd,tr) 
            end

  and parse_id (nil) = (print "Error in parse id\n"; raise idlErr)
     | parse_id (lst) =
  case lst of
       ID ide :: tr => 
       let val (id, tc) = parse_id(tr);
       in (ide::id, tc)
       end
     | COMMA :: tr => 
       let val (id, tc) = parse_id(tr);
       in (id, tc) 
       end
     | COLON :: tr => (nil, tr)
     | _ => (print "Error in parse id\n"; raise idlErr)

  and parse_program (nil) =(print " Error in Program\n"; raise progErr)
    | parse_program (lst) =
  case lst of 
       PROGRAM::ID ide :: IS :: BEGIN :: tr => let val (cmds,ts)=parse_cmds(tr)
                                               in case ts of
                                                       [END] => (PROG(CMDLST(cmds)))
                                                     |_ => (print "Not finished the program!\n";raise progErr)
                                               end
       | _ => (print "Expect PROGRAM HEADER!\n";raise progErr);

fun readin(infile:string) =
let val inf = TextIO.openIn infile
val lexer = makeLexer( fn n => valOf(inputLine( inf ) ))
fun mklst (END) = END::nil | mklst (v) = v::mklst(lexer())
val lst = mklst(lexer())
in lst 
end

