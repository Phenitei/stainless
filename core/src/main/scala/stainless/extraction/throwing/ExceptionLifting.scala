/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package throwing

trait ExceptionLifting extends inox.ast.SymbolTransformer { self =>
  val s: Trees
  val t: oo.Trees

  def transform(symbols: s.Symbols): t.Symbols = {

    oo.SymbolTransformer(new inox.ast.TreeTransformer {
      val s: self.s.type = self.s
      val t: self.t.type = self.t
      implicit val syms = symbols

      override def transform(e: s.Expr): t.Expr = e match {

        /* Encode the predicate in the throwing inside a pattern match in the ensuring */
        case s.Throwing(tBody, thrPred) => tBody match {
            case s.Ensuring(eBody, ensPred) => matchInEnsuring(eBody, thrPred, ensPred)
            case _ => matchInEnsuring(tBody, thrPred, s.Lambda(Seq.empty, s.BooleanLiteral(true)))
        }

        /* Replace an if-throw-else-body or if-body-else-throw construct by an if left else right */
        case s.IfExpr(cond, thenn @ s.Throw(ex), elze) => {
          val leftType = s.getLeftType(ex.getType) match {
            case Some(tpe) => this.transform(tpe)
            case _ => throw new IllegalStateException("Could not find Left type!")
          }

          val rightType = s.getRightType(elze.getType) match {
            case Some(tpe) => this.transform(tpe)
            case _ => throw new IllegalStateException("Could not find Right type!")
          }

          t.IfExpr(this.transform(cond),
            t.ClassConstructor(leftType.asInstanceOf[t.ClassType], Seq(this.transform(ex))),
            t.ClassConstructor(rightType.asInstanceOf[t.ClassType], Seq(this.transform(elze))))
        }

        case s.IfExpr(cond, thenn, elze @ s.Throw(ex)) => {
          val leftType = s.getLeftType(ex.getType) match {
            case Some(tpe) => this.transform(tpe)
            case _ => throw new IllegalStateException("Could not find Left type!")
          }

          val rightType = s.getRightType(elze.getType) match {
            case Some(tpe) => this.transform(tpe)
            case _ => throw new IllegalStateException("Could not find Right type!")
          }

          t.IfExpr(this.transform(cond),
            t.ClassConstructor(rightType.asInstanceOf[t.ClassType], Seq(this.transform(thenn))),
            t.ClassConstructor(leftType.asInstanceOf[t.ClassType], Seq(this.transform(ex))))

        }

        /* try to find the call site of the function throwing the exception
        case s.Try(tBody, cases, finallizer) => ???
        */

          /* TODO :
           * * Put the result of the function call in a Right. !! C'est plus complique, check le papelard !!
           * * Deal with other functions calling me.
           * * Deal with types.
           */
        case _ => super.transform(e)
      }

      def matchInEnsuring(body: s.Expr, leftPred: s.Lambda, rightPred: s.Lambda): t.Expr = {
        /* Compute all the types we will need to build the pattern match */
        val nBody = this.transform(body)

        val exceptionType = s.getExceptionType match {
          case Some(tpe) => tpe
          case _ => throw new IllegalStateException("Could not find Exception type!")
        }

        val eitherType = s.getEitherType(exceptionType, body.getType) match {
          case Some(tpe) => this.transform(tpe)
          case _ => throw new IllegalStateException("Could not find Either type!")
        }

        val leftType = s.getLeftType(exceptionType) match {
          case Some(tpe) => this.transform(tpe)
          case _ => throw new IllegalStateException("Could not find Left type!")
        }

        val rightType = s.getRightType(body.getType) match {
          case Some(tpe) => this.transform(tpe)
          case _ => throw new IllegalStateException("Could not find Right type!")
        }

        val eRes: t.ValDef = t.ValDef(FreshIdentifier("eRes", alwaysShowUniqueID = true), eitherType)

        /* Build the pattern match between Left[Exception](res) => leftPred(res) and Right[A](res) => rightPred(res) */
        val pred = t.Lambda(Seq(eRes), t.MatchExpr(nBody, Seq(
          t.MatchCase(
            t.ClassPattern(None, leftType.asInstanceOf[t.ClassType],
              Seq(t.WildcardPattern(Some(t.ValDef(FreshIdentifier("res", alwaysShowUniqueID = true), this.transform(exceptionType)))))),
            None, t.Application(this.transform(leftPred), Seq(nBody))),
          t.MatchCase(
            t.ClassPattern(None, rightType.asInstanceOf[t.ClassType],
              Seq(t.WildcardPattern(Some(t.ValDef(FreshIdentifier("res", alwaysShowUniqueID = true), this.transform(body.getType)))))),
            None, t.Application(this.transform(rightPred), Seq(nBody)))
          )))

        t.exprOps.withPostcondition(nBody, Some(pred))
      }

    }).transform(symbols)
  }
}
