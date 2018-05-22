/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package throwing

/* TODO :
 * * Try to deal with non-explicit exceptions, such as division by zero, etc...
 * * Fix that every function that throws needs a throwing and vice-versa: ideally, one could hope that one without the
 *   other would warn the user instead of catching fire.
 * * Deal with cases where a try/catch body contains more code than a throwing function, where we must find the call
 *   site (if it exists) of the vulnerable function, pattern match against it's result, and check that the corresponding
 *   exception is caught.
 *
 * Notes to self/reader:
 * * Only `if - cond - throw - else - body` and `if - cond - body - else - throw` are recognized; this means that
 *   functions that use the throw keyword must contain this form as their returning statement.
 * * Every function with a `throw` must have a throwing, and every function with a throwing must have a throw, else
 *   things will go FUBAR.
 * * The above means that operators that throw an exception non explicitly (such as `x / 0`) aren't lifted.
 * * I used the haskell « Right is right » convention for the results: we use Either[Exception, NormalResult].
 * * The predicate in a `throwing` is added inside the `ensuring`, under a pattern match of the form
 *       case Left(e)  => (throwingPredicate)(e)
 *       case Right(r) => (previous ensuring predicate -- `true` if there was none)(r)
 * *
 */
trait ExceptionLifting extends inox.ast.SymbolTransformer { self =>
  val s: Trees
  val t: oo.Trees

  def transform(symbols: s.Symbols): t.Symbols = {

    oo.SymbolTransformer(new inox.ast.TreeTransformer {
      val s: self.s.type = self.s
      val t: self.t.type = self.t
      implicit val syms: s.Symbols = symbols

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
            case e => throw new IllegalStateException("Could not find Left type: " + e)
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

        case s.Try(tBody, cases, None) => ???

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
