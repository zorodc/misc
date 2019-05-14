#include <variant>
#include <string>
#include <memory>
#include <cctype>
#include <tuple>
#include <ostream>
#include <functional>
#include <type_traits>
#include <unordered_map>
#include <iomanip>  /* std::boolalpha      */
#include <iostream> /* std::cout, std::cin */
/*
 * A small lisp interpreter implemented in C++, using the standard library.
 *
 * This was mostly an experiment, to see what could be done w/ std::variant
 *  and std::shared_ptr, which provide most of what's necessary
 *  for a lisp runtime: primitive garbage collection and runtime tagging.
 *
 * These components get you quite far, though not quite there.
 * They do get you the respective elements, a type system and memory management,
 *  without having to implement these things yourself.
 * The former is easier to implement oneself than the latter in C++;
 * Therefore, whilst implementing lisp in Java might be easier, as one can
 *  leverage the garbage collector, std::shared_ptr offers some substitute.
 *
 * Additionally, one finds that compiler errors w/ std::variant are atrocious.
 *
 * There's still a lot to add, before this can be used for anything:
 * TODO: dot-cons-notation in input.
 * TODO: Clean up some of the code a bit, wherever possible.
 * TODO: Make the exception handling a bit more robust.
 * TODO: Provide error messages whenever an exception is met.
 */

/*
 * Basic types and operations.
 */
namespace lisp {
	struct Cel; /* forward-decl of cons-cell */
	struct FNS; /* forward-decl of fn-struct */

	using  LFn = std::shared_ptr< FNS >;
	using  Ptr = std::shared_ptr< Cel >;
	using  Int =   long long;
	using  Str = std::string;
	using  Sym = std::tuple<std::string>;
	using  Val = std::variant<bool, Int, Sym, Str, Ptr, LFn>;

	using Namespace = std::unordered_map<std::string, Val>;
	struct Cel { Val Car, Cdr; Cel(Val ca, Val cd) : Car{ca}, Cdr{cd} {} };
	struct FNS { std::function<Val(Ptr, Namespace&, Ptr)> evl; Ptr body; };

	namespace exceptions {
		/* Lexer exceptions. */
		struct unexpected { char           which; };
		struct badinteger { std::string_view bad; };
		struct early_eofs { std::string_view bad; }; /* Early EOF. */


		/* Eval exceptions. */
		struct nullp_args { }; /* Arg was Nil when this wasn't appropriate.   */
		struct wrong_type { }; /* Arg was of an unexpected type.              */
		struct wrong_form { }; /* A special form's syntax wasn't adhered to.  */
		struct wrong_acnt { }; /* Arity of a function call is incorrect.      */
	}

	namespace check {
		template <class T>
		inline void TAG(Val v) { if (!std::holds_alternative<T>(v))
		                                 throw exceptions::wrong_type{}; }
		inline void NUL(Ptr p) { if (!p) throw exceptions::nullp_args{}; }
	}

	Ptr Lexr (const Str& sexp); /* Retuns conscell AST from a string's s-expr */
	Val Eval (const Ptr& sast, Namespace& n); /* Returns an AST's evaluation. */
	Val Eval (const Val& sast, Namespace& n);

	static const Ptr Nil = Ptr{nullptr};
	inline Val& Car (Ptr Obj)      { check::NUL(Obj);  return Obj->Car; }
	inline Val& Cdr (Ptr Obj)      { check::NUL(Obj);  return Obj->Cdr; }
	inline auto Cons(Val f, Val s) { return std::make_shared<Cel>(f,s); }
	inline Sym  Symbolize(std::string&& str) { return {std::move(str)}; }

	inline auto Call(const LFn& f, Namespace& n, Ptr a) {
		return f->evl(a, n, f->body);
	}

	inline Ptr  Eval_List(Ptr args, Namespace& n, unsigned* c = nullptr) {
		if (!args) return lisp::Nil;
		return Cons(Eval(Car(args), n),
		            Eval_List(std::get<Ptr>(Cdr(args)), n, c ? (*c)++, c : c));
	}
}

namespace func {
	inline auto Fst(lisp::Val c){return     lisp::Car(std::get<lisp::Ptr>(c)); }
	inline auto Snd(lisp::Val c){return Fst(lisp::Cdr(std::get<lisp::Ptr>(c)));}
	inline auto Nth(lisp::Val c, unsigned N) {
		while (N--) c = lisp::Cdr(std::get<lisp::Ptr>(c));
		return Fst (c);
	}
}

/*
 * METAPROGRAMMING
 */
namespace meta {

	/* A type to allow template parameter T of pack::operator() to be deduced. */
	template <unsigned N> struct proxy { enum { value = N }; };

	/* Instantiate template R with a parameter pack of N different T args. */
	template <typename T, template <typename...> class R, typename... Ts>
	struct pack {
		template <unsigned N> auto operator()(proxy<N> = {}) {
			if constexpr (N) return pack<T,R,Ts...,T>{}(proxy<N-1>{});
			else             return        R<Ts...  >();
		}
	};

	template <typename... Ts>
	struct unwrapper {
		template <typename FN> auto untyped(FN fn, const lisp::Ptr& args) {
			unsigned i = sizeof...(Ts);
			return fn( Ts{func::Nth(args, --i)}... );
		}

		template <typename FN> auto checked(FN fn, const lisp::Ptr& args) {
			unsigned i = sizeof...(Ts);
			return fn( std::get<Ts>(func::Nth(args, --i))... );
		}
	};


	template <typename T, typename... Ts>
	struct last_of_pack { using type = typename last_of_pack<Ts...>::type; };
	template <typename Last> struct last_of_pack<Last>{ using type = Last; };

	/*
	 * Call a function w/ some lisp::Val arguments contained in a lisp list.
	 */
	template <unsigned Arity, typename FN>
	auto Untyped_Dispatch(FN fn, const lisp::Ptr& args) {
		return pack<lisp::Val, unwrapper>{}(proxy<Arity>{}).untyped(fn, args);
	}

	/*
	 * Call a function w/ some typed arguments contained in a lisp list.
	 */
	template <unsigned Arity, typename... Ts>
	auto Checked_Dispatch(auto fn, const lisp::Ptr& args) {
		using last_type  = typename last_of_pack<Ts...>::type;
		const auto Addnl = Arity - sizeof...(Ts);

		return pack<last_type, unwrapper, Ts...>{}(proxy<Addnl>{}).checked(fn, args);
	}
}

/*
 * Helpers for defining functions, using the metaprograming stuff.
 */
namespace def {

	/* Used for defining functions which control their evaluation order. */
	inline lisp::LFn Builtin(
		 std::function<lisp::Val(lisp::Ptr, lisp::Namespace&, lisp::Ptr)> fn,
		 lisp::Ptr body = lisp::Nil) {
		using namespace lisp;
		return std::make_shared<FNS>(FNS{fn, std::move(body)});
	}

	template <unsigned Arity, typename FN>
	lisp::LFn Untyped(FN fn) {
		return Builtin([=](lisp::Ptr args, lisp::Namespace& n, lisp::Ptr _) {
		    unsigned cnt = 0; auto ev = Eval_List(args, n, &cnt);

		    if (cnt != Arity) throw lisp::exceptions::wrong_acnt{};
		    try { return lisp::Val{meta::Untyped_Dispatch<Arity>(fn, ev)}; }
		    catch (...) { throw lisp::exceptions::wrong_type{}; }
		});
	}

	template <unsigned Arity, typename... Ts>
	lisp:: LFn Checked(auto fn) {
		return Builtin([=](lisp::Ptr args, lisp::Namespace& n, lisp::Ptr _) {
			unsigned cnt = 0; auto ev = Eval_List(args, n, &cnt);

			if (cnt != Arity) throw lisp::exceptions::wrong_acnt{};
			try { return lisp::Val{meta::Checked_Dispatch<Arity, Ts...>(fn, ev)}; }
			catch (...) { throw lisp::exceptions::wrong_type{}; }
		});
	}
}

static std::ostream& operator<<(std::ostream& o, const lisp::Val& v)
{
	o << std::boolalpha;
	std::visit([&](auto&& arg) {
		using T = std::decay_t<decltype(arg)>;
		     if constexpr (std::is_same_v<T, lisp::Str>) o << '"' << arg << '"';
		else if constexpr (std::is_same_v<T, lisp::Sym>) o << std::get<0> (arg);
		else if constexpr (std::is_same_v<T, lisp::Ptr>) {
			o << '(';
			const lisp::Ptr *lastelm = nullptr, *p;
			for (p = &arg; p && *p; p = std::get_if<lisp::Ptr>(&lisp::Cdr(*p))) {
				lastelm = p;
				if  (p != &arg) o << ' ';

				o << lisp::Car(*p);
			}

			if (!p && lastelm) o << " . " << lisp::Cdr(*lastelm);
			o << ')';
		} else o << arg; }, v);
	return o;
}

/*
 * Functions for use in the language itself, and a hash table to hold them.
 */
namespace func {
	inline auto Last(lisp::Val lv) {
		auto l = std::get<lisp::Ptr>(lv);

		while (lisp::Cdr(l) != lisp::Val{lisp::Nil})
			l = std::get<lisp::Ptr>(lisp::Cdr(l));
		return lisp::Car(l);
	}

	inline auto Zip(lisp::Ptr a, lisp::Ptr b) {
		if (a == lisp::Nil && b == lisp::Nil) return lisp::Nil;
		else return lisp::Cons(lisp::Cons(Fst(a), lisp::Cons(Fst(b), lisp::Nil)),
		 Zip(std::get<lisp::Ptr>(lisp::Cdr(a)),
		     std::get<lisp::Ptr>(lisp::Cdr(b))));
	}

	lisp::Namespace Lang = {
		{{"true"}, true},
		{{"false"}, false},
		{{"nil"}, lisp::Val{lisp::Nil}},

		{{"car" }, def::Checked<1, lisp::Ptr>([](lisp::Ptr c) { return lisp::Car(c); })},
		{{"cdr" }, def::Checked<1, lisp::Ptr>([](lisp::Ptr c) { return lisp::Cdr(c); })},
		{{"cons"}, def::Untyped<2>([](lisp::Val x, lisp::Val y) {
					return lisp::Val{lisp::Cons(x, y)}; })},
		{{"+"}, def::Checked<2, lisp::Int>([](lisp::Int x, lisp::Int y) { return x+y; })},
		{{"-"}, def::Checked<2, lisp::Int>([](lisp::Int x, lisp::Int y) { return x-y; })},
		{{"*"}, def::Checked<2, lisp::Int>([](lisp::Int x, lisp::Int y) { return x*y; })},
		{{"/"}, def::Checked<2, lisp::Int>([](lisp::Int x, lisp::Int y) { return x/y; })},
		{{"%"}, def::Checked<2, lisp::Int>([](lisp::Int x, lisp::Int y) { return x%y; })},
		{{"<"}, def::Checked<2, lisp::Int>([](lisp::Int x, lisp::Int y) { return x<y; })},
		{{"="}, def::Untyped<2> ([](lisp::Val x, lisp::Val y) { return x==y; })},

		{{"eval"},  def::Builtin([](lisp::Ptr arg, lisp::Namespace& n, lisp::Ptr _) {
					return lisp::Call(def::Untyped<1>(
					   [&](lisp::Val obj) { return lisp::Eval (obj, n); }), n, arg);
				})},
		{{"quote"}, def::Builtin([](lisp::Ptr arg, lisp::Namespace& n, lisp::Ptr _) {
					return Fst(arg); })},
		{{"if"},    def::Builtin([](lisp::Ptr arg, lisp::Namespace& n, lisp::Ptr _) {
			auto testp = lisp::Car(arg);
			try {
				auto ifp = std::get   <lisp::Ptr>( lisp::Cdr(arg));
				auto elp = std::get_if<lisp::Ptr>(&lisp::Cdr(ifp));
				auto res = std::get<bool>(lisp::Eval(testp, n));
				if (!res && elp) return lisp::Eval(lisp::Car(*elp), n); // TODO: Poor exception use
				else             return lisp::Eval(lisp::Car( ifp), n);
			} catch (...) { throw lisp::exceptions::wrong_type{}; }
		})},

		{{"let"}, def::Builtin([](lisp::Ptr lexpr, lisp::Namespace& n, lisp::Ptr _) {
			auto union_shadow = [&](lisp::Ptr pairs) -> lisp::Namespace {
				auto newns = n;
				try {
					for (auto it = pairs; it != lisp::Nil;
					          it = std::get<lisp::Ptr>(lisp::Cdr(it))) {
						auto lpair = lisp::Car(it);
						auto metav = Fst(lpair), sexpr = Snd(lpair);
						auto bound = lisp::Eval(sexpr, newns); // TODO: Poor exception use
						newns[std::get<0>(std::get<lisp::Sym>(metav))] = bound;
					}
				} catch (...) { throw lisp::exceptions::wrong_form{}; }

				return newns;
			};

			try {
				auto n = union_shadow(std::get<lisp::Ptr>(lisp::Car(lexpr)));
				return Last(lisp::Eval_List(
					            std::get<lisp::Ptr>(lisp::Cdr(lexpr)), n)); // TODO: Poor exception use
			} catch (...) { throw lisp::exceptions::wrong_form{}; }
		})},

		{{"defun"}, def::Builtin([](lisp::Ptr args, lisp::Namespace& n, lisp::Ptr _) {
			auto body = lisp::Cdr(args);

			try {
				auto alst =             std::get<lisp::Ptr>(lisp::Car(args));
				auto name = std::get<0>(std::get<lisp::Sym>(lisp::Car(alst)));
				auto mvar =             std::get<lisp::Ptr>(lisp::Cdr(alst));
				return n[name] = def::Builtin(
					// TODO: Insert checks.
				    [=](lisp::Ptr args, lisp::Namespace& n, lisp::Ptr body) {
						auto binds = func::Zip(mvar, args);
						return lisp::Eval(lisp::Cons(lisp::Sym{"let"},
						                  lisp::Cons(binds, body)), n);
				    }, std::get<lisp::Ptr>(body)); // TODO: Poor exception use

			} catch (...) { throw lisp::exceptions::wrong_form{}; }
		})}
	};
}

/*
 * Lexing/parsing implementation.
 */

using size = unsigned long;
lisp::Ptr lisp::Lexr (const lisp::Str& sexp)
{
	auto expect = [&](size i, char req) {
		if (sexp[i] != req) throw lisp::exceptions::unexpected{sexp[i]}; };

	auto intlit = [&](size i, size& next) {
		auto s = sexp.substr(i);
		next   = i;
		Val retval;
		try { retval = std::stoll(s, &i); } catch (...) {
			throw lisp::exceptions::badinteger{s.substr(i)}; }
		next += i;
		return retval;
	};

	auto strlit = [&](size i, size& next) {
		expect(i++, '\"'); /* Sanity check. */
		for (size c = i; c < sexp.length(); ++c)
			switch (sexp[c]) {
			case '\\': ++c;  break;
			case  '"':
				next = c + 1;
				return sexp.substr(i, c-i);
			}
		throw lisp::exceptions::early_eofs{{sexp.c_str() + i, sexp.length()}};
	};

	auto isidch = [ ](char c) { return isgraph(c) && c != '(' && c != ')'; };
	auto symbol = [&](size i, size& next) {
		if (!isidch(sexp[i])) expect(i, '\0');
		size c = i;

		while (isidch(sexp[c])) c++;

		next = c;
		return lisp::Symbolize(sexp.substr(i, c-i));
	};

	auto skipws = [&](size i, size& next) {
		while (sexp[i] ==  ' ' ||
		       sexp[i] == '\t' ||
		       sexp[i] == '\n') ++i;
		next = i;
	};

	std::function<lisp::Val(size i, size& next)> expr; /* "forward-decl" */

	auto oquote = [&](size i, size& next) {
		++next; return lisp::Cons(lisp::Sym("quote"),
		               lisp::Cons(expr(i+1, next), lisp::Nil));
	};

	auto conses = [&](size i, size& next) {
		expect(i++, '('); /* Sanity check. */

		lisp::Ptr  list = lisp::Nil;
		lisp::Ptr* last = &list;
		for (size c = i; c < sexp.length(); skipws(c, c))
			if   (sexp[c] == ')') { next = c+1; return list; }
			else {
				*last = lisp::Cons(expr(c, c), lisp::Nil);
				 last = &std::get<Ptr>(lisp::Cdr(* last));
			}

		throw lisp::exceptions::early_eofs{{sexp.c_str() + i, sexp.length()}};
	};

	expr = [&](size i, size& next) -> lisp::Val { skipws(i, i);
		switch (sexp[i]) {
		case '0': case '1': case '2': case '3': case '4':
		case '5': case '6': case '7': case '8':
		case '9': return intlit(i, next);
		case '(': return conses(i, next);
		case'\"': return strlit(i, next);
		case'\'': return oquote(i, next);
		default : return symbol(i, next);

		/* Prevent inputs from being interpreted in odd ways. */
		case ')': throw lisp::exceptions::unexpected{sexp[i]};
		}
	};

	size _; return lisp::Cons(expr(0, _), lisp::Nil);
}

lisp::Val lisp::Eval (const lisp::Val& ast, lisp::Namespace& n) {
	if (std::holds_alternative<Sym>(ast)) {
		auto   it  = n.find(std::get<0>(std::get<Sym>(ast)));
		return it != std::end(n) ? it->second : lisp::Nil; /* TODO: Change. */
	}

	return std::holds_alternative<Ptr>(ast) ? Eval(std::get<Ptr>(ast), n) : ast;
}

lisp::Val lisp::Eval (const lisp::Ptr& ast, lisp::Namespace& n) {
	Val fn = std::visit([&](auto&& e) {
		using T = std::decay_t<decltype(e)>;
		if (std::is_same_v<T, Ptr> || std::is_same_v<T, Sym>) return Eval(e, n);
		else                                                  return Val{ Nil };
	}, lisp::Car(ast));

	auto vp = std::get_if<LFn>(&fn);
	if (!vp) throw lisp::exceptions::wrong_type{}; /* TODO: Throw to indicate !callable. */

	return lisp::Call(*vp, n, std::get<Ptr>(lisp::Cdr(ast)));
}

/* Read an expression by ensuring parens match, notifying a functor on line break. */
template <typename FN>
std::string naive_read_expr (std::istream& s, FN line_break_callback) {
	unsigned op = 0,
	         cp = 0;
	std::string exp;
	char        chr;
	bool    saw_tok = false; /* Saw something other than whitespace? */
	do {
		exp  += (chr = s.get());
		if (s.eof()) return exp;

		saw_tok |= chr != ' ' && chr != '\t' && chr != '\n';
		     if (chr == '(') ++op;
		else if (chr == ')') ++cp;
		else if (chr == '\n' && saw_tok) line_break_callback(op-cp);
	} while (!saw_tok || op > cp);

	/* Parse the remainder of the line. */
	std::string tmp; std::getline(s, tmp);
	exp += tmp;
	return exp;
}

int main() {
	for(;;) {
		std::string expr = naive_read_expr(std::cin,
			[] (unsigned d) {
				std::cout << ">";
				while (d--) std::cout << ' ';
			});

		if (!std::cin || expr == "exit") break;
		lisp::Val parsetree;
		try { parsetree = lisp::Car(lisp::Lexr(expr)); } catch (...)
		    { std::cerr << "Lexer error!\n"; continue; }

		try   { std::cout << lisp::Eval(parsetree, func::Lang) << '\n'; }
		catch (lisp::exceptions::wrong_form&) { std::cerr << "Bad form syntax.\n"; }
		catch (lisp::exceptions::wrong_acnt&) { std::cerr << "Incorrect arity.\n"; }
		catch (lisp::exceptions::wrong_type&) { std::cerr << "Incorrect types.\n"; }
		catch (lisp::exceptions::nullp_args&) { std::cerr << "Incorrectly nil.\n"; }
		catch (...)                           { std::cerr << "Some eval error.\n"; }
	}
}
