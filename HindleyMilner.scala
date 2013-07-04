/*
 * http://dysphoria.net/code/hindley-milner/HindleyMilner.scala
 * Andrew Forrest
 *
 * Implementation of basic polymorphic type-checking for a simple language.
 * Based heavily on Nikita Borisov’s Perl implementation at
 * http://web.archive.org/web/20050420002559/www.cs.berkeley.edu/~nikitab/courses/cs263/hm.html
 * which in turn is based on the paper by Luca Cardelli at
 * http://lucacardelli.name/Papers/BasicTypechecking.pdf
 *
 * If you run it with "scala HindleyMilner.scala" it will attempt to report the types
 * for a few example expressions. (It uses UTF-8 for output, so you may need to set your
 * terminal accordingly.)
 *
 * Do with it what you will.
 */

abstract class SyntaxNode
case class Lambda(v: String, body: SyntaxNode) extends SyntaxNode
case class Ident(name: String) extends SyntaxNode
case class Apply(fn: SyntaxNode, arg: SyntaxNode) extends SyntaxNode
case class Let(v: String, defn: SyntaxNode, body: SyntaxNode) extends SyntaxNode
case class Letrec(v: String, defn: SyntaxNode, body: SyntaxNode) extends SyntaxNode

object SyntaxNode {
	def string(ast: SyntaxNode): String = {
		if (ast.isInstanceOf[Ident])
			nakedString(ast)
		else
			"("+nakedString(ast)+")"
	}

	def nakedString(ast: SyntaxNode) = ast match {
		case i: Ident => i.name
		case l: Lambda => "fn "+l.v+" ⇒ "+string(l.body)
		case f: Apply => string(f.fn)+" "+string(f.arg)
		case l: Let => "let "+l.v+" = "+string(l.defn)+" in "+string(l.body)
		case l: Letrec => "letrec "+l.v+" = "+string(l.defn)+" in "+string(l.body)
	}
}

class TypeError(msg: String) extends Exception(msg)
class ParseError(msg: String) extends Exception(msg)


object TypeSystem {

	type Env = Map[String, Type]

	abstract class Type
	case class Variable(id: Int) extends Type {
		var instance: Option[Type] = None
		lazy val name = nextUniqueName
	}
	case class Oper(name: String, args: Seq[Type]) extends Type
	def Function(from: Type, to: Type) = Oper("→", Array(from, to))
	val Integer = Oper("int", Array())
	val Bool = Oper("bool", Array())

	var _nextVariableName = 'α';
	def nextUniqueName = {
		val result = _nextVariableName
		_nextVariableName = (_nextVariableName.toInt + 1).toChar
		result.toString
	}
	var _nextVariableId = 0
	def newVariable: Variable = {
		val result = _nextVariableId
		_nextVariableId += 1
		Variable(result)
	}

	def string(t: Type): String = t match {
		case v: Variable => v.instance match {
			case Some(i) => string(i)
			case None => v.name
		}
		case Oper(name, args) => {
			if (args.length == 0)
				name
			else if (args.length == 2)
				"("+string(args(0))+" "+name+" "+string(args(1))+")"
			else
				args.mkString(name + " ", " ", "")
		}
	}


	def analyse(ast: SyntaxNode, env: Env): Type = analyse(ast, env, Set.empty)
	def analyse(ast: SyntaxNode, env: Env, nongen: Set[Variable]): Type = ast match {
		case Ident(name) => gettype(name, env, nongen)
		case Apply(fn, arg) => {
			val funtype = analyse(fn, env, nongen)
			val argtype = analyse(arg, env, nongen)
			val resulttype = newVariable
			unify(Function(argtype, resulttype), funtype)
			resulttype
		}
		case Lambda(arg, body) => {
			val argtype = newVariable
			val resulttype = analyse(body, 
									 env + (arg -> argtype),
									 nongen + argtype)
			Function(argtype, resulttype)
		}
		case Let(v, defn, body) => {
			val defntype = analyse(defn, env, nongen)
			val newenv = env + (v -> defntype)
			analyse(body, newenv, nongen)
		}
		case Letrec(v, defn, body) => {
			val newtype = newVariable
			val newenv = env + (v -> newtype)
			val defntype = analyse(defn, newenv, nongen + newtype)
			unify(newtype, defntype)
			analyse(body, newenv, nongen)
		}
	}

	def gettype(name: String, env: Env, nongen: Set[Variable]): Type = {
		if (env.contains(name))
			fresh(env(name), nongen)

		else if (isIntegerLiteral(name))
			Integer

		else
			throw new ParseError("Undefined symbol "+name)
	}

	def fresh(t: Type, nongen: Set[Variable]) = {
		import scala.collection.mutable
		val mappings = new mutable.HashMap[Variable, Variable]
		def freshrec(tp: Type): Type = {
			prune(tp) match {
				case v: Variable =>
					if (isgeneric(v, nongen))
						mappings.getOrElseUpdate(v, newVariable)
					else
						v

				case Oper(name, args) =>
					Oper(name, args.map(freshrec(_)))
			}
		}

		freshrec(t)
	}



	def unify(t1: Type, t2: Type) {
		val type1 = prune(t1)
		val type2 = prune(t2)
		(type1, type2) match {
			case (a: Variable, b) => if (a != b) {
				if (occursintype(a, b))
					throw new TypeError("recursive unification")
				a.instance = Some(b)
			}
			case (a: Oper, b: Variable) => unify(b, a)
			case (a: Oper, b: Oper) => {
				if (a.name != b.name ||
					a.args.length != b.args.length) throw new TypeError("Type mismatch: "+string(a)+"≠"+string(b))
				
				for(i <- 0 until a.args.length)
					unify(a.args(i), b.args(i))
			}
		}
	}


	// Returns the currently defining instance of t.
	// As a side effect, collapses the list of type instances.
	def prune(t: Type): Type = t match {
		case v: Variable if v.instance.isDefined => {
			var inst = prune(v.instance.get)
			v.instance = Some(inst)
			inst
		}
		case _ => t
	}

	// Note: must be called with v 'pre-pruned'
	def isgeneric(v: Variable, nongen: Set[Variable]) = !(occursin(v, nongen))

	// Note: must be called with v 'pre-pruned'
	def occursintype(v: Variable, type2: Type): Boolean = {
		prune(type2) match {
			case `v` => true
			case Oper(name, args) => occursin(v, args)
			case _ => false
		}
	}

	def occursin(t: Variable, list: Iterable[Type]) =
		list exists (t2 => occursintype(t, t2))

	val checkDigits = "^(\\d+)$".r
	def isIntegerLiteral(name: String) = checkDigits.findFirstIn(name).isDefined

}

object HindleyMilner {

	def main(args: Array[String]){
		Console.setOut(new java.io.PrintStream(Console.out, true, "utf-8"))

		val var1 = TypeSystem.newVariable
		val var2 = TypeSystem.newVariable
		val pairtype = TypeSystem.Oper("×", Array(var1, var2))

		val var3 = TypeSystem.newVariable

		val myenv: TypeSystem.Env = Map.empty ++ Array(
			"pair" -> TypeSystem.Function(var1, TypeSystem.Function(var2, pairtype)),
			"true" -> TypeSystem.Bool,
			"cond" -> TypeSystem.Function(TypeSystem.Bool, TypeSystem.Function(var3, TypeSystem.Function(var3, var3))),
			"zero" -> TypeSystem.Function(TypeSystem.Integer, TypeSystem.Bool),
			"pred" -> TypeSystem.Function(TypeSystem.Integer, TypeSystem.Integer),
			"times"-> TypeSystem.Function(TypeSystem.Integer, TypeSystem.Function(TypeSystem.Integer, TypeSystem.Integer))
		)


		val pair = Apply(Apply(Ident("pair"), Apply(Ident("f"), Ident("4"))), Apply(Ident("f"), Ident("true")))
		val examples = Array[SyntaxNode](
			// factorial
			Letrec("factorial", // letrec factorial =
				Lambda("n",    // fn n =>
					Apply(
						Apply(   // cond (zero n) 1
							Apply(Ident("cond"),     // cond (zero n)
								Apply(Ident("zero"), Ident("n"))),
							Ident("1")),
						Apply(    // times n
							Apply(Ident("times"), Ident("n")),
							Apply(Ident("factorial"),
								Apply(Ident("pred"), Ident("n")))
						)
					)
				),      // in
				Apply(Ident("factorial"), Ident("5"))
			),

			// Should fail:
			// fn x => (pair(x(3) (x(true)))
			Lambda("x",
				Apply(
					Apply(Ident("pair"),
						Apply(Ident("x"), Ident("3"))),
					Apply(Ident("x"), Ident("true")))),

			// pair(f(3), f(true))
			Apply(
				Apply(Ident("pair"), Apply(Ident("f"), Ident("4"))), 
				Apply(Ident("f"), Ident("true"))),


			// letrec f = (fn x => x) in ((pair (f 4)) (f true))
			Let("f", Lambda("x", Ident("x")), pair),

			// fn f => f f (fail)
			Lambda("f", Apply(Ident("f"), Ident("f"))),

			// let g = fn f => 5 in g g
			Let("g",
				Lambda("f", Ident("5")),
				Apply(Ident("g"), Ident("g"))),

			// example that demonstrates generic and non-generic variables:
			// fn g => let f = fn x => g in pair (f 3, f true)
			Lambda("g",
				   Let("f",
					   Lambda("x", Ident("g")),
					   Apply(
							Apply(Ident("pair"),
								  Apply(Ident("f"), Ident("3"))
							),
							Apply(Ident("f"), Ident("true"))))),

			// Function composition
			// fn f (fn g (fn arg (f g arg)))
			Lambda("f", Lambda("g", Lambda("arg", Apply(Ident("g"), Apply(Ident("f"), Ident("arg"))))))
		)
		for(eg <- examples){
			tryexp(myenv, eg)
		}
	}

	def tryexp(env: TypeSystem.Env, ast: SyntaxNode) {
		print(SyntaxNode.string(ast) + " : ")
		try {
			val t = TypeSystem.analyse(ast, env)
			print(TypeSystem.string(t))

		}catch{
			case t: ParseError => print(t.getMessage)
			case t: TypeError => print(t.getMessage)
		}
		println
	}
}

HindleyMilner.main(argv)
