/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package throwing

trait ExceptionLifting extends inox.ast.SymbolTransformer { self =>
  val s: Trees
  val t: oo.Trees

  def transform(symbols: s.Symbols): t.Symbols = {

    // FIXME: encode exceptions!
    oo.SymbolTransformer(new inox.ast.TreeTransformer {
      val s: self.s.type = self.s
      val t: self.t.type = self.t

      override def transform(e: s.Expr): t.Expr = {
        if (s.exprOps.hasSpec(e)) {
          ???
        } else super.transform(e)
      }

    }).transform(symbols)
  }
}
