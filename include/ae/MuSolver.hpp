#ifndef MUSOLVER__HPP__
#define MUSOLVER__HPP__
#include <assert.h>

#include "ae/SMTUtils.hpp"
#include "ae/AeValSolver.hpp"
#include "ufo/Smt/EZ3.hh"

using namespace std;
using namespace boost;

namespace ufo
{
  class MuSolver
  {
    private:
      Expr flaMain;
      Expr flaRel;
      Expr fla;
      Expr flaForall;
      Expr flaOrig;
      ExprMap nonrecDefs;
      ExprMap recDefsMu;
      ExprMap recDefsNu;
      ExprMap recDefsBinders;
      ExprVector fixVars;
      Expr muVar;
      Expr nuVar;
      ExprFactory& efac;
      SMTUtils u;
      bool usedNu;
      int name_id = 0;
      bool debug = true;

    public:
      MuSolver(ExprFactory& _efac): efac(_efac), u(_efac) {}

    //typedef std::vector<ExprPair> ExprEqs;
    // non-recursive version (don't be confused with ExprSimpl.hpp::getConj(Expr a, ExprSet &conjs))
    static inline void getConjV(Expr s, ExprVector& ops)
    {
      if (isOpX<AND>(s))
      {
        for (unsigned i = 0; i < s->arity(); i++)
        {
          ops.push_back(s->arg(i));
        }
      }
      else ops.push_back(s);
    }

    //    static inline bool rewrite(Expr a, Expr b, Expr& fla)
    bool rewrite(Expr a, Expr b, Expr& fla)
    {
      ExprVector av;
      filter (a, bind::IsConst (), inserter(av, av.begin()));

      ExprMap matching;
//         myprintf("rewrite: comparing \n");
//                 myprint(a);
//                 myprintf("and \n");
//                 Expr tmp = fla;
//                myprint(tmp);
      if (findMatchingSubexpr (a, fla, av, matching))
      {
//        myprintf("matched\n");
//        print_matching(matching);
        Expr toRepl1 = a;
        Expr toRepl2 = b;
        {
          toRepl1 = replaceAll(toRepl1, matching);
          toRepl2 = replaceAll(toRepl2, matching);
        }
        fla = replaceAll(fla, toRepl1, toRepl2);
//        myprint(fla);
        return true;
      }
      return false;
    }

    Expr get_definition(Expr head) 
    {
      Expr binders = recDefsBinders[head];
      Expr tmp = nonrecDefs[head];
      if(tmp!=NULL){
        return replaceAll(binders, binders->last(), mk<EQ>(head,tmp));
        //return mk<FORALL>(binders, mk<EQ>(head, tmp2));
      } else {
        tmp = recDefsMu[head];
        if(tmp!=NULL) {
            return replaceAll(mk<AND>(muVar, binders), binders->last(), mk<EQ>(head,tmp));
          //return mk<AND>(muVar, mk<FORALL>(binders, mk<EQ>(head, tmp)));
        } else {
            return replaceAll(mk<AND>(nuVar, binders), binders->last(), mk<EQ>(head,recDefsNu[head]));
          //return mk<AND>(nuVar, mk<FORALL>(binders, mk<EQ>(head, recDefsNu[head])));
        }
      }
    }

    void print(Expr & fla)
    {
      Expr fla2 = fla;
      if (usedNu) fla2 = mk<AND>(nuVar, fla);
      else fla2 = mk<AND>(muVar, fla);

      // serialize everything:
      // outs () << "(declare-fun mu () Bool)\n(declare-fun nu () Bool)\n";
      u.serialize_formula(flaMain);
      u.serialize_formula(simplifyArithm(fla2));
    }
    void printall()
    {
      // serialize everything:
      // outs () << "(declare-fun mu () Bool)\n(declare-fun nu () Bool)\n";
      for(auto it = fixVars.begin(); it!=fixVars.end(); ++it) {
        Expr tmp = *it;
        if (isOpX<FAPP>(tmp)) {
          u.print(tmp->arg(0));
          //printf("\n");
          outs() << " \n";
        }
      }
      printf("(declare-fun mu () Bool)\n");
      printf("(declare-fun nu () Bool)\n");
      u.serialize_formula(flaMain);
      //u.serialize_formula(simplifyArithm(fla2));
      for(auto it = fixVars.begin(); it!=fixVars.end(); ++it) {
        Expr tmp = *it;
        //myprintf("trying to print the definition for\n");
        //myprint(tmp);
        Expr e = get_definition(*it);
        u.serialize_formula(e);
        //printf("\n");
        outs() << "\n";
      }
    }

    void myprintf(string s)
    {
      if (debug) printf("%s", s.c_str());
    }
    void myprint(const Expr & fla)
    {
      if(debug) {
        u.print(fla);
        myprintf("\n");
      }
    }
    void print_matching(ExprMap matching)
    {
      if(debug) {
        myprintf("matching\n");
      for (auto & m : matching) {
        if (m.first!=NULL && m.second != NULL) {
        Expr tmp1 = m.first;
        Expr tmp2 = m.second;
        myprint(tmp1);
        myprintf("-->\n");
        myprint(tmp2);
        }
        //else if (m.first!=NULL) {
        //Expr tmp1 = m.first;
        //myprint(tmp1);
        //myprintf("-->null\n");
        //}
      }
      }
    }
    void myprint_eqs(ExprEqs eqs)
    {
      if(debug) {
        for (auto it = eqs.begin(); it!=eqs.end(); ++it) {
        Expr tmp1 = it->first;
        Expr tmp2 = it->second;
        myprint(tmp1);
        myprintf("==\n");
        myprint(tmp2);
        }
      }
    }
    void myprint_eq(ExprPair eq)
    {
      if(debug) {
        Expr tmp1 = eq.first;
        Expr tmp2 = eq.second;
        myprint(tmp1);
        myprintf("==\n");
        myprint(tmp2);
      }
    }

    void myprintdisj(ExprSet & disj)
    {
      if(debug) {
      Expr fla = disjoin(disj, efac);
      u.print(fla);
      myprintf("\n");
      }
    }

    void myprintvec(ExprVector & vars)
    {
      if(debug) {
        for (auto it = vars.begin(); it != vars.end();++it) {
          Expr tmp = *it;
          myprint(tmp);
        }
      }
    }
    void myprintset(ExprSet & vars)
    {
      if(debug) {
        for (auto it = vars.begin(); it != vars.end();++it) {
          Expr tmp = *it;
          myprint(tmp);
        }
      }
    }

    void myprintconj(ExprSet & conj)
    {
      if(debug) {
      Expr fla = conjoin(conj, efac);
      u.print(fla);
      myprintf("\n");
      }
    }

    void update_definition(Expr head, Expr body)
    {
      myprintf("updating the definition for\n");
      myprint(head);
      myprint(body);
        Expr binders = recDefsBinders[head];
        if (usedNu) {
          recDefsNu[head] = body;
        } else {
          recDefsMu[head] = body;
        }
        nonrecDefs[head] = NULL;
    }

    void add_definition(Expr head, Expr body, bool nu)
    {
      myprintf("adding the definition for\n");
      myprint(head);
      myprint(body);
      ExprVector args;
      filter(head, bind::IsConst (), inserter(args, args.begin()));
      ExprVector args1;
      for(auto it=args.begin(); it!=args.end(); ++it) {
        Expr v = *it;
        Expr type=bind::typeOf(v);
        args1.push_back(bind::constDecl(v,type));
      }
      args1.push_back(mk<EQ>(head,body));
      Expr forallExp = mknary<FORALL>(args1);
      recDefsBinders[head]=forallExp;
        if (nu) {
          recDefsNu[head] = body;
        } else {
          recDefsMu[head] = body;
        }
    }

    void initialize(Expr s)
    {
      ExprFactory& efac = s->getFactory();
      ExprVector cnjs;
      getConjV(s, cnjs);

      for (auto c : cnjs)
      {
        if (isOpX<FORALL>(c))
        {
          c = regularizeQF(c);
          if (isOpX<FAPP>(c->last()))
          {
            flaMain = c;
            flaRel = c->last();
          }
          if (isOpX<EQ>(c->last()))
          {
            flaForall = c;
            fla = c->last();
            fixVars.push_back(c->last()->first());
            nonrecDefs[c->last()->left()] = c->last()->right();
            recDefsBinders[c->last()->left()] = c;
          }
        }

        if (isOpX<AND>(c) && isOpX<FORALL>(c->right())
            && isOpX<EQ>(c->right()->last()))
        {
          Expr var = c->left();
          string pref = lexical_cast<string>(var);
          c = regularizeQF(c->right());
          if (pref == "mu")
          {
            Expr def = c->last()->right();
            for (auto & a : recDefsNu)
              if (contains (def, a.first->left())) {
                printf("Alternations between mu and nu are currently unsupported\n");
                exit(0);
              }
            recDefsMu[c->last()->left()] = def;
            recDefsBinders[c->last()->left()] = c;
            fixVars.push_back(c->last()->left());
            muVar = var;
          }
          if (pref == "nu")
          {
            Expr def = c->last()->right();
            for (auto & a : recDefsMu)
              if (contains (def, a.first->left())) {
                printf("Alternations between mu and nu are currently unsupported\n");
                exit(0);
              }
            recDefsNu[c->last()->left()] = def;
            recDefsBinders[c->last()->left()] = c;
            fixVars.push_back(c->last()->left());
            nuVar = var;
          }
        }
      }

      assert(flaRel == fla->left());

      usedNu = false;
      flaOrig = fla;
      fla = fla->right();
    }

    bool iter()
    {
      SMTUtils u(efac);
      ExprSet flaOrigDisj;
      getDisj(flaOrig->right(), flaOrigDisj);
      fla = normalizeArithm(fla);
      ExprSet flaApps;
      filter (fla, bind::IsFApp (), inserter(flaApps, flaApps.begin()));
      ExprMap allRepls;
      for (auto & app : flaApps)
      {
        Expr appRepled = app;
        bool repled = false; // should not allow replacing same app more than once
        for (auto & a : recDefsMu)
          if (!repled) repled = rewrite(a.first, a.second, appRepled);

        for (auto & a : recDefsNu)
        {
          if (!repled) repled = rewrite(a.first, a.second, appRepled);
          usedNu |= repled;
        }
        allRepls[app] = appRepled;
      }

      fla = replaceAll(fla, allRepls);
      fla = expandExists(fla);
      fla = simplifyExists(fla);
      fla = expandConjSubexpr(fla);
      ExprSet flaUpdDisj;
      getDisj(fla, flaUpdDisj);

      Expr ex1;
      Expr ex2;
      ExprSet usedOrig;
      ExprSet usedUpd;
      ExprMap forallMatching;
      bool hasFapps = false;

      map <Expr, ExprVector> all;
      map <Expr, ExprVector> usedTmp;
      for (auto & a : flaOrigDisj)
      {
        for (auto & b : flaUpdDisj)
        {
          ExprSet tmp;
          getConj(b, tmp);
          for (auto it = tmp.begin(); it != tmp.end();)
          {
            if ((isOpX<EXISTS>(a) && isOpX<EXISTS>(*it)) ||
                (isOpX<FAPP>(a) && isOpX<FAPP>(*it) && a->left() == (*it)->left()))
            {
              it = tmp.erase(it);
              all[a].push_back(conjoin(tmp, efac));
              usedTmp[a].push_back(b);
            }
            else ++it;
          }
        }
      }

      ExprVector commonSubset;
      bool first = true;
      for (auto & a : all)
      {
        if (first) {
          first = false;
          commonSubset = a.second;
          continue;
        }

        for (auto it = commonSubset.begin(); it != commonSubset.end();)
        {
          if (find(a.second.begin(), a.second.end(), *it) == a.second.end())
            it = commonSubset.erase(it);
          else ++it;
        }
      }

      Expr comm = conjoin(commonSubset, efac);

      ExprSet toSearchRem;
      Expr matchNeedToBeFound;

      if (u.isFalse(comm)) comm = mk<TRUE>(efac);
      if (isOpX<TRUE>(comm))
      {
        // try to simplify further
        fla = expandDisjSubexpr(fla);
        flaUpdDisj.clear();
        getDisj(fla, flaUpdDisj);
      }
      else
      {
        ExprSet finl;
        for (auto & a : all)
        {
          ExprVector tmp = a.second;
          bool found = false;
          for (auto & b : tmp)
          {
            if (b == comm)
            {
              found = true;
              for (auto & c : usedTmp[a.first])
              {
                if (contains(c, comm))
                {
                  flaUpdDisj.erase(c);
                  finl.insert(simplifyBool(replaceAll(c, comm, mk<TRUE>(efac))));
                }
              }
            }
          }
        }

        if (!u.implies(mkNeg(comm), disjoin(flaUpdDisj, efac)))
        {
          // outs () << "unable to create abstraction\n";
          return false;
        }

        toSearchRem = flaUpdDisj;
        flaUpdDisj = finl;
      }

      // finding forallMatching
      for (auto it = flaUpdDisj.begin(); it != flaUpdDisj.end();)
      {
        if (isOpX<EXISTS>(*it))
        {
          if (ex2 != NULL) exit(0); // unsupported
          ex2 = *it;
          it = flaUpdDisj.erase(it);
        }
        else ++it;
      }

      for (int i = 0; i < 2; i++) // try scanning two times (sometimes it's hard to find matches)
        for (auto it = flaOrigDisj.begin(); it != flaOrigDisj.end();)
        {
          if (!isOpX<FAPP>(*it))
          {
            if (isOpX<EXISTS>(*it))
            {
              ex1 = *it;
              it = flaOrigDisj.erase(it);
            }
            else ++it;
            continue;
          }
          hasFapps = true;
          ExprVector av;
          filter (*it, bind::IsConst (), inserter(av, av.begin()));
          Expr a = normalizeArithm(replaceAll(*it, forallMatching));
          bool found = false;
          for (auto it2 = flaUpdDisj.begin(); it2 != flaUpdDisj.end();)
          {
            if (!isOpX<FAPP>(*it2))
            {
              ++it2;
              continue;
            }
            Expr d = normalizeArithm(*it2);
            myprintf("comparing \n");
            myprint(a);
            myprintf("and \n");
            myprint(d);
            ExprMap matching1;
            if (findMatchingSubexpr (a, d, av, matching1))
            {
              myprintf("matching found\n");
              int toCont = false;
              for (auto & m : matching1)
              {
                if (m.first != NULL && m.second != NULL)
                {
                  Expr tmp = replaceAll (m.second, forallMatching);
                  if (forallMatching[m.first] != NULL &&
                      forallMatching[m.first] != tmp)
                  {
                    toCont = true;
                    break;
                  }
                  if (forallMatching[m.first] == NULL)
                  {
                    forallMatching[m.first] = m.second;
                  }
                }
              }
              if (toCont)
              {
                ++it2;
                continue;
              }

              usedUpd.insert(*it2);

              it2 = flaUpdDisj.erase(it2);
              found = true;
              break;
            }
            ++it2;
          }
          if (found)
          {
            usedOrig.insert(*it);
            it = flaOrigDisj.erase(it);
          }
          else ++it;
        }

      if(!u.isEquiv(disjoin(usedUpd, efac),
                       replaceAll(disjoin(usedOrig, efac), forallMatching)))
        return false;

      if (!forallMatching.empty() && ex1 == NULL && ex2 == NULL)
      {
        bool sanityCheck = false;
        for (auto & m : forallMatching)
          if (m.first != NULL && m.second != NULL)
          {
            sanityCheck = true;
          }
        if (!sanityCheck) return false;

        Expr extr;
        if (!flaUpdDisj.empty())
        {
          if (flaOrigDisj.empty())
          {
            extr = disjoin(flaUpdDisj, efac);
          }
          else
          {
            Expr whatsLeftOrig = replaceAll(disjoin(flaOrigDisj, efac), forallMatching);
            Expr whatsLeftUpd = disjoin(flaUpdDisj, efac);
            for (auto & a : recDefsNu)
              if (contains (whatsLeftOrig, a.first->left())) return false;
            for (auto & a : recDefsMu)
              if (contains (whatsLeftOrig, a.first->left())) return false;

            if (!u.implies(whatsLeftOrig, whatsLeftUpd))
            {
              if (u.implies(whatsLeftUpd, whatsLeftOrig))
                extr = disjoin(flaUpdDisj, efac);
              else
                return false;
            }
            flaUpdDisj.clear();
          }
        }

        if (isOpX<TRUE>(comm))
        {
          if (extr == NULL)
          {
            fla = replaceAll(flaForall, flaForall->last(),
                           mk<EQ>(flaOrig->left(), replaceAll(flaRel, forallMatching)));
          } else {
            fla = replaceAll(flaForall, flaForall->last(),
                             mk<EQ>(flaOrig->left(), mk<OR>(extr, replaceAll(flaRel, forallMatching))));
          }
        }
        else
        {
          fla = replaceAll(flaForall, flaForall->last(),
                           mk<EQ>(flaOrig->left(), mk<OR>(mkNeg(comm),
                                  mk<AND>(comm, replaceAll(flaRel, forallMatching)))));
        }
        print(fla);
        return true;
      }

      // validate exist
      if ((!forallMatching.empty() || !hasFapps) && ex1 != NULL && ex2 != NULL)
      {
        ExprVector av;
        if (hasFapps)
        {
          for (unsigned i = 0; i < ex1->arity() - 1; i++)
            av.push_back(bind::fapp(ex1->arg(i)));
        }
        else
        {
          filter (ex1->last(), bind::IsConst (), inserter(av, av.begin()));
        }

        ex1 = replaceAll(ex1, forallMatching);
        ex2 = normalizeArithm(ex2);

        ExprSet cnjs1, cnjs2;
        getConj(ex1->last(), cnjs1);
        getConj(ex2->last(), cnjs2);
        if (!flaOrigDisj.empty()) cnjs1.insert(disjoin(flaOrigDisj, efac));
        if (!toSearchRem.empty()) cnjs2.insert(disjoin(toSearchRem, efac));

        ExprMap existsMatching;
        for (auto it1 = cnjs1.begin(); it1 != cnjs1.end(); )
        {
          bool doBreak = false;
          for (auto it2 = cnjs2.begin(); it2 != cnjs2.end(); )
          {
            ExprMap m1 = existsMatching;
            if (findMatchingSubexpr (*it1, *it2, av, m1))
            {
              existsMatching = m1;
              it1 = cnjs1.erase(it1);
              it2 = cnjs2.erase(it2);
              doBreak = true;
              break;
            }
            else ++it2;
          }
          if (!doBreak) ++it1;
        }

        for (auto & m : existsMatching)
          if (m.first != NULL && m.second != NULL)
          {

            Expr tmp = cloneVar(m.first, mkTerm<std::string> (lexical_cast<string>(m.first)+"_tmp", efac));
            Expr tmp1 = mk<EQ>(tmp, m.second);
            ExprSet v;
            filter (m.second, bind::IsConst (), inserter(v, v.begin()));
            AeValSolver ae(mk<TRUE>(efac), tmp1, v, false, false);
            if (ae.solve())
            {
              outs() << "  Surjectivity sanity failed: " << *m.first << "  <-->  " << *m.second << "\n";
              exit(0);
            }
          }

        Expr whatsLeft = replaceAll(conjoin(cnjs1, efac), existsMatching);
        Expr match = conjoin(cnjs2, efac);
        if (u.implies(match, whatsLeft))
        {
          // currently, an incomplete search here
          if (cnjs1.empty()) // that is, whatsLeft == true
          {
            // do nothing
          }
          else if (u.implies(match, whatsLeft))
          {
            flaUpdDisj.clear();
          }
          else
          {
            // TODO: find a subset of "match" that is equivalent to whatsLeft and remove
          }

          Expr upd = replaceAll(replaceAll(flaRel, forallMatching), existsMatching);
          flaUpdDisj.insert(upd);
          if (isOpX<TRUE>(comm))
          {
            fla = replaceAll(flaForall, flaForall->last(), mk<EQ>(flaOrig->left(),
                        disjoin(flaUpdDisj, efac)));
          } else {
            fla = replaceAll(flaForall, flaForall->last(), mk<EQ>(flaOrig->left(),
                        mk<OR>(mkNeg(comm), mk<AND>(comm, disjoin(flaUpdDisj, efac)))));
          }
          print(fla);
          return true;
        }
      }

      return false;
    };

    Expr unfold(Expr e)
    {
      Expr e1;
      e = normalizeArithm(e);
      myprintf("unfolding\n");
      myprint(e);
      ExprSet flaApps;
      filter (e, bind::IsFApp (), inserter(flaApps, flaApps.begin()));
      ExprMap allRepls;
      for (auto & app : flaApps)
      {
        // myprintf("trying to unfold\n");
        Expr appRepled = app;
        bool repled = false; // should not allow replacing same app more than once
        for (auto & a : recDefsMu) {
          Expr tmp = a.first;
          if (!repled) repled = rewrite(a.first, a.second, appRepled);
        };

        for (auto & a : recDefsNu)
        {
          if (!repled) repled = rewrite(a.first, a.second, appRepled);
          usedNu |= repled;
        }
        allRepls[app] = appRepled;
      }
      
      e1 = replaceAll(e, allRepls);
      myprintf("unfolded\n");
      myprint(e1);
      return e1;
    }

    Expr mkVar(string s) {
      return bind::intConst(mkTerm<string> (s, efac));
    }
    Expr mkInt(int n){
      return mkTerm(mpz_class(n), efac);
    }

    bool isEqual(Expr e1, Expr e2)
    {
      myprintf("isEqual\n");
      myprint(e1);
      myprintf("and\n");
      myprint(e2);
      return !u.isSat(mk<NEQ>(e1,e2));
    }

    bool check_sat(Expr e, vector<int> args)
    {
      // myprintf("check sat\n");
      // myprint(e);
      ExprVector argExprs;
      for (int arg : args)
      {
        // myprintf(to_string(arg) + " ");
        argExprs.push_back(mkInt(arg));
      }
      ExprMap map;
      for (int i = 1; i < e->arity(); ++i)
      {
        map.insert(make_pair(e->arg(i), argExprs.at(i-1)));
      }
      /*
      Expr target = mk<IMPL>(replaceAll(e,map),mk<FALSE>(efac));
      myprint(target);
      if (u.isSat(target))
        myprintf("sat\n");
      else 
        myprintf("unsat\n");
      myprintf("\n");
      */
      return true;
    }

    Expr lemma_search(Expr e) 
    {
      myprintf("lemma search\n");
      myprint(e);
      ExprSet flaApps;
      ExprMap defs;
      defs.insert(recDefsMu.begin(), recDefsMu.end());
      defs.insert(recDefsNu.begin(), recDefsNu.end());
      const Expr undef = mkVar("undef");

      // make pred-unfold map
      map<Expr,ExprMap> predUnfoldMap;
      filter (e, bind::IsFApp (), inserter(flaApps, flaApps.begin()));
      for (auto & app : flaApps)
      {
        for (auto & def : defs)
        {
          ExprVector vars;
          ExprMap matching;
          filter(def.first, bind::IsConst(), inserter(vars,vars.begin()));
          if (findMatchingSubexpr(def.first, app, vars, matching)) 
          {
            Expr replaced;
            // print_matching(matching);
            replaced = replaceAll(def.second, matching);
            ExprVector vars2;
            ExprMap matching2;
            filter(app, bind::IsConst(), inserter(vars2, vars2.begin()));
            if (findMatchingSubexpr(app, replaced, vars2, matching2))
            {
              predUnfoldMap.insert(make_pair(app, matching2));
            }
          }
        }
      }

      Expr confPredUnfolded;
      Expr refinedPred;

      // get pred with conflicting substitution
      ExprMap tempSubs;
      Expr confPred;
      bool confCheck = false;
      for (const auto & predUnfold : predUnfoldMap)
      {
        myprintf("predUnfold\n");
        myprint(predUnfold.first);
        print_matching(predUnfold.second);
        
        bool check = true;
        //  myprintf("match\n");
        //  print_matching(match);
        //  myprintf("match printed\n");
        for (auto & pair : tempSubs)
        {
          if (pair.second == NULL) continue;
          for (const auto & pair_ : predUnfold.second)
          {
            if (pair_.second == NULL) continue;
            myprint(pair.first);
            myprint(pair_.first);
            myprint(pair.second);
            myprint(pair_.second);
            
            if (isEqual(pair.first,pair_.first) && !isEqual(pair.second,pair_.second)) 
            {
              myprintf("conflict\n");
              check = false;
              break;
            }
          }
        }
        if (check)
        {
          tempSubs.insert((predUnfold.second).begin(), (predUnfold.second).end());
          // myprintf("match(2)\n");
          // print_matching(match);
        }
        else
        {
          // conflict
          if (!confCheck)
          {
            confCheck = true;
            confPred = predUnfold.first;
            ExprMap tempMap;
            tempMap.insert((predUnfold.second).begin(), (predUnfold.second).end());
            confPredUnfolded = replaceAll(predUnfold.first, tempMap);
          }
          else myprintf("more than one conflicts\n");
        }
      }

      if (!confCheck)
      {
        myprintf("no conflict\n");
        return unfold(e);
      }
      // set undef and replace
      ExprVector vars;
      filter(confPred, bind::IsConst(), inserter(vars, vars.begin()));
      ExprVector preUndefs;
      ExprMap argToUndef;
      for (auto & var : vars)
      {
        bool check = true;
        for (auto & pair : tempSubs)
        {
          if (pair.first == NULL || pair.second == NULL) {
            continue;
          }
          myprint(pair.first);
          myprint(var);
          if (pair.first == var)
          {
            myprintf("same\n");
            check = false;
            break;
          }
        }
        // if var doesnt belong to map as lhs
        if (check)
        {
           preUndefs.push_back(var);
        }
      }
      for (auto & var : preUndefs)
      {
        for (int i = 0; i < confPred->arity(); ++i)
        {
          if(contains(confPred->arg(i),var))
          {
            argToUndef.insert(make_pair(confPred->arg(i),undef));
          }
        }
      }
      refinedPred = replaceAll(confPred, argToUndef);
      refinedPred = replaceAll(refinedPred, tempSubs);

      // 
      myprintf("pred1\n");
      myprint(confPredUnfolded);
      myprintf("pred2\n");
      myprint(refinedPred);
      Expr tempDef;
      for (auto & def : defs)
      {
        if (isOpX<FAPP>(refinedPred) && isOpX<FAPP>(def.first))
        {
          if (refinedPred->left() == def.first->left())
          {
            tempDef = def.first;
          }
        }
        else 
        {
          myprintf("something wrong\n");
          return unfold(e);
        }
      }
      myprintf("tempDef\n");
      myprint(tempDef);
      ExprVector newArgs(tempDef->arity());
      ExprMap newArgsMap;
      for (int i = 1; i < tempDef->arity(); ++i)
      {
        newArgs.at(i) = normalizeArithm(mk<PLUS>(tempDef->arg(i), mk<MINUS>(refinedPred->arg(i),confPredUnfolded->arg(i))));
        if (contains(newArgs.at(i),undef))
        {
          newArgs.at(i) = undef;
        }
        myprintf("newArgs("+to_string(i)+")\n");
        myprint(newArgs.at(i));
        newArgsMap.insert(make_pair(tempDef->arg(i), newArgs.at(i)));
      }
      Expr prevLemma = replaceAll(tempDef,newArgsMap);
      myprint(prevLemma);

      int arity = tempDef->arity()-1;
      int thres = 10;
      vector<int> vec(arity,0);
      while(vec.at(arity-1) != thres)
      {
        check_sat(tempDef,vec);
        vec.at(0)++;
        for (int i = 0; i < arity-1; ++i)
        {
          if (vec.at(i) == thres)
          {
            vec.at(i) = 0;
            vec.at(i+1)++;
          }
        }
      }

      return unfold(e);
    }

    Expr flex_unfold(Expr e)
    {
      Expr e1;
      e = normalizeArithm(e);
      myprintf("flex unfolding\n");
      myprint(e);
      ExprSet flaApps;
      filter (e, bind::IsFApp (), inserter(flaApps, flaApps.begin()));
      ExprMap allRepls;
      map<Expr,map<Expr,Expr>> constDiffByItr;
      
      // get diffs for defs
      ExprMap defs;
      defs.insert(recDefsMu.begin(), recDefsMu.end());
      defs.insert(recDefsNu.begin(), recDefsNu.end());
      for (auto & def : defs) 
      {
        ExprVector vars;
        ExprMap matching;
        filter (def.first, bind::IsConst(), inserter(vars,vars.begin()));
        if (findMatchingSubexpr(def.first, def.second, vars, matching))
        {
          for (auto & var : vars)
          {
            Expr minusTerm = mk<MINUS>(matching[var], var);
            Expr normTerm = normalizeArithm(minusTerm);
            ExprVector tempVec;
            // myprintf("  var\n  ");
            // myprint(var);
            // myprintf("  diff\n");
            // myprint(norm_term);
            filter (normTerm, bind::IsConst(), inserter(tempVec,tempVec.begin()));
            if (tempVec.size() == 0)
            {
              // myprintf("empty\n");
              constDiffByItr[def.first][var] = normTerm;
            } else {
              // myprintf("have var\n");
              constDiffByItr[def.first][var] = mkVar("undef");
            }
            // myprintf("  isNumeric\n");
            // if (isNumeric(norm_term))
            //   myprintf("  true\n");
            // else
            //   myprintf("  false\n");
            // Expr termtype = bind::typeOf(norm_term);
            // myprintf("  type\n");
            // myprint(termtype);
          }

        }
        myprint(def.first);
        myprint(def.second);
        print_matching(constDiffByItr[def.first]);
      }
      //
      
      // make equations 
      ExprEqs eqs;
      ExprVector eqVars;
      ExprMap unfoldCount;
      int i = 0;
      for (auto & app: flaApps)
      {
        bool varflag = false;

        // diff : map<Expr,map<Expr,Expr>>
        for (auto & diff : constDiffByItr) {
          ExprVector vars;
          ExprMap matching;
          Expr pred = diff.first;
          filter (pred , bind::IsConst(), inserter(vars,vars.begin()));
          if (findMatchingSubexpr (pred,app,vars,matching))
          {
            myprintf("found matching subexpr\n");
            print_matching(matching);
            // diff_by_var : map<Expr,Expr>
            for (auto & diffByVar : diff.second)
            {
              Expr undef = mkVar("undef");
              Expr idvar = mkVar("v"+to_string(i));
              unfoldCount[app] = idvar;
              Expr lhs;
              ExprVector vars;
              filter (matching[diffByVar.first], bind::IsConst(), inserter(vars,vars.begin()));
              ExprMap tempMap;
              for (auto & var : vars)
              {
                tempMap[var] = cloneVar(var, mkTerm<string>(lexical_cast<string>(var)+"_tmp", efac));
              }
              lhs = replaceAll(matching[diffByVar.first],tempMap);
              // Expr lhs = cloneVar(diffByVar.first, mkTerm<string>(lexical_cast<string>(diffByVar.first)+"_tmp", efac));
              // diffByVar.first ... y
              // matching[diffByVar.first] ... y+z
              Expr rhs = (diffByVar.second == undef) 
                ? (undef)
                : (mk<PLUS>(mk<MULT>(diffByVar.second,idvar),matching[diffByVar.first]));
              // Expr eq = mk<EQ>(lhs,rhs);
              // myprint(eq);
              if (rhs != undef) 
              {
                eqs.push_back(make_pair(lhs,rhs));
                if (!varflag)
                {
                   eqVars.push_back(idvar);
                   varflag = true;
                }
              }
            }
          }
        }
        ++i;
      }
      myprintf("eqVars\n");
      myprintvec(eqVars);
      //

      myprintf("eqs\n");
      myprint_eqs(eqs);
      // solve eqs
      //  elim vars
      ExprVector elimVars;
      ExprEqs elimRes;
      ExprMap elimSubs;
      for (auto & eq : eqs)
      {
        filter (eq.first, bind::IsConst(), inserter(elimVars, elimVars.begin()));
        for (auto & elimVar : elimVars)
        {
          if (eq.first == elimVar && elimSubs.count(eq.first) == 0)
          {
            elimSubs[eq.first] = eq.second;
          }
        }
//        auto varItr = find_if (elimVars.begin(), elimVars.end(), [=](pair<Expr,Expr> v){ return v.first == eq.first; });
//        if (varItr != elimVars.end())
//          elimRes.push_back (make_pair((*varItr).second,eq.second));
//        else
//          elimVars.push_back(eq);
      }
      for (auto & eq : eqs)
      {
        Expr substituted = replaceAll(eq.first, elimSubs);
        elimRes.push_back(make_pair(substituted,eq.second));
      }
      myprintf("elim result\n");
      myprint_eqs(elimRes);
      //  simplify
      ExprVector simpRes;
      for (auto & eq : elimRes)
      {
        // simpRes.push_back (mk<EQ> (mkTerm(mpz_class(0), efac), normalizeArithm (mk<MINUS> (eq.first,eq.second))));
        simpRes.push_back (normalizeArithm(mk<EQ>(eq.first,eq.second)));
      }
      myprintf("simp result\n");
      myprintvec(simpRes);

      //  call solver
      ExprMap solved;
      Expr eqConj = mk<TRUE>(efac);
      for (auto & eq : simpRes) 
      {
        eqConj = mk<AND>(eqConj,eq);
      }
      // ExprSet vars;
      // filter (eq, bind::IsConst(), inserter(vars,vars.begin()));
      // myprintf("filtered\n");
      // for (auto & var : vars) 
      for (auto & eqVar : eqVars) 
      {
        eqConj = mk<AND>(mk<LT>(mkTerm(mpz_class(0),efac),eqVar), eqConj);
      }
      myprintf("eq made\n");
      myprint(eqConj);
      EZ3 ez3(efac);
      ZSolver<EZ3> smt(ez3);
      smt.assertExpr(eqConj);
      if(smt.solve()) 
      {
        printf("solved\n");
        ZSolver<EZ3>::Model m = smt.getModel();
        // for (auto & var : vars)
        for (auto & eqVar : eqVars)
        {
          Expr expr = m.eval(eqVar);
          solved[eqVar] = expr;
          myprint(eqVar);
          myprint(expr);
        }
      }
      else
      {
        printf("not solved\n");
        return lemma_search(e);
      }

      // unfold
      Expr unfolded = e;
      for (auto & app : flaApps)
      {
        ExprMap repls;
        Expr appRepled = app;
        Expr appItr = app;
        EZ3 ez3(efac);
        int count;
        if (unfoldCount.count(app) != 0 && solved.count(unfoldCount[app]) != 0 )
        {
          std::string countStr = ez3.toSmtLib(solved[unfoldCount[app]]);
          try 
          {
            count = std::stoi(countStr);
          }
          catch (...)
          {
            std::cout << countStr;
            printf("caught\n");
            count = 1;
          }
        }
        else 
        {
          count = 1;
        }
        for (int i = 0; i < count; i++)
        {
          repls[appItr] = unfold(appItr);
          appItr = repls[appItr];
          /*
          appRepled = appItr;
          bool repled = false;
          // myprint(appRepled);
          // if (unfoldCount.count(app) != 0 && solved.count(unfoldCount[app]) != 0 )
          // {
          //   myprint(unfoldCount[app]);
          //   myprint(solved[unfoldCount[app]]);
          // }
          for (auto & a : recDefsMu) {
            Expr tmp = a.first;
            if (!repled) repled = rewrite(a.first, a.second, appRepled);
          };
    
          for (auto & a : recDefsNu)
          {
            if (!repled) repled = rewrite(a.first, a.second, appRepled);
            usedNu |= repled;
          }
          repls[appItr] = appRepled;
          unfolded = replaceAll(unfolded,repls);
          appItr = appRepled;
          */
          unfolded = replaceAll(unfolded,repls);
          myprintf("multiple unfold\n");
          myprintf("  i\n");
          printf("%d\n", i);
          myprintf("  appItr\n");
          myprint(appItr);
          myprintf("  appRepled\n");
          myprint(appRepled);
          myprintf("  unfolded\n");
          myprint(unfolded);
        }
      }
      unfolded = normalizeArithm(unfolded);

      myprintf("unfolded\n");
      myprint(unfolded);
      return unfolded;
    }

    ExprSet simplify_conj(ExprSet es)
    {
      for (auto it = es.begin(); it != es.end();++it) {
        for (auto it2 = es.begin(); it2 != es.end();) {
          myprintf("checking subsumption\n");
          Expr tmp1 = *it;
          Expr tmp2 = *it2;
          myprint(tmp1);
          myprint(tmp2);
          if (!(*it == *it2) && u.implies(*it, *it2)) {
            myprintf("the latter subsumed\n");
            it2 = es.erase(it2);
          } else {
            ++it2;
          }
        };
      };
      myprintconj(es);
      return es;
    }

    ExprSet simplify_disj(ExprSet es)
    {
      for (auto it = es.begin(); it != es.end();++it) {
        for (auto it2 = es.begin(); it2 != es.end();) {
          myprintf("checking subsumption\n");
          Expr tmp1 = *it;
          Expr tmp2 = *it2;
          myprint(tmp1);
          myprint(tmp2);
          if (!(*it == *it2) && u.implies(*it2, *it)) {
            myprintf("the latter subsumed\n");
            it2 = es.erase(it2);
          } else {
            ++it2;
          }
        };
      };
      return es;
    }

    bool iter_or()
    {
      SMTUtils u(efac);
      ExprSet flaOrigDisj;
      myprintf("start folding disjunctions\n");
      myprint(flaRel);
      myprintf("=\n");
      myprint(fla);
      ExprVector freevars;
      ExprVector freevars0;
      ExprMap renaming;
      ExprMap renaming_inv;

      filter (flaRel, bind::IsConst (), inserter(freevars, freevars.begin()));
      for (auto it = freevars.begin(); it != freevars.end();++it) {
        Expr tmp = *it;
        Expr tmp0 = cloneVar(tmp, mkTerm<std::string> (lexical_cast<string>(tmp)+"_tmp", efac));
        freevars0.push_back(tmp0);
        renaming[tmp] = tmp0;
        renaming_inv[tmp0] = tmp;
      };
      Expr flaOrigRenamed = replaceAll(flaOrig, renaming);
      Expr flaRelRenamed = replaceAll(flaRel, renaming);
      myprintf("renamed\n");
      myprint(flaRelRenamed);
      myprint(flaOrigRenamed);

      getDisj(flaOrigRenamed, flaOrigDisj);
      fla = normalizeArithm(fla);

      fla = flex_unfold(fla);
      fla = expandExists(fla);
      fla = simplifyExists(fla);
      //fla = expandConjSubexpr(fla);
      fla = expandDisjSubexpr(fla);
      //myprint(fla);
      ExprSet flaUpdDisj;
      ExprSet flaUpdConj;
      getConj(fla, flaUpdConj);
      myprintf("step 1\n");
      myprintdisj(flaOrigDisj);
      myprint(fla);

      Expr ex1;
      Expr ex2;
      ExprSet used;
      bool hasFapps = false;
      bool simplified = false;

      map <Expr, ExprVector> all;
      map <Expr, ExprVector> usedTmp;
      ExprSet transformed;
      ExprSet constrdisj;
      for (auto it = flaOrigDisj.begin(); it != flaOrigDisj.end();)
      {
        if (!isOpX<FAPP>(*it))
          {
            constrdisj.insert(*it);
            it = flaOrigDisj.erase(it);
          }
        else ++it;
      }
      Expr constr = disjoin(constrdisj,efac);
      myprintf("constraints filtered\n");
      myprint(constr);
      myprintdisj(flaOrigDisj);
      for (auto b = flaUpdConj.begin(); b!=flaUpdConj.end(); ++b)
      {
        ExprMap forallMatching;
        ExprEqs eqs;
        bool foundall = true;
        //ExprSet usedOrig;
        ExprSet usedUpd{};
        ExprSet flaUpdDisj;
        getDisj(*b, flaUpdDisj);
        for (auto it = flaOrigDisj.begin(); it != flaOrigDisj.end();)
        {
          if (!isOpX<FAPP>(*it))
          {
            return false;
          }
          hasFapps = true;
          ExprVector av;
          filter (*it, bind::IsConst (), inserter(av, av.begin()));
          Expr a = normalizeArithm(replaceAll(*it, forallMatching));
          //Expr a = normalizeArithm(*it);
          bool found = false;
          for (auto it2 = flaUpdDisj.begin(); it2 != flaUpdDisj.end();)
          {
            //myprintf("flaUpdDisj \n");
            //myprintdisj(flaUpdDisj);
            if (!isOpX<FAPP>(*it2))
            {
              ++it2;
              continue;
            }
            Expr d = normalizeArithm(*it2);
            myprintf("comparing \n");
            myprint(a);
            myprintf("and \n");
            myprint(d);
            if (findMatchingSubexpr2 (a, d, av, eqs))
            {
              myprintf("matching found\n");
              int toCont = false;
              it2 = flaUpdDisj.erase(it2);
              found = true;
              break;
            }
            ++it2;
          };
          //myprint(*it);
          ++it;
          if (!found )
            {foundall=false; break;};
        };
        if(foundall) {
              myprintf("all matching found\n sovling:\n");
            myprint_eqs(eqs);
            ExprVector exvars0; // empty
            ExprVector exvars1; // empty
            bool r = solve_eqs(eqs,freevars0,freevars,exvars0,exvars1,forallMatching);
            if(r) {
              print_matching(forallMatching);
              Expr constr0 = replaceAll(constr, forallMatching);
              Expr constr1 = replaceAll(disjoin(flaUpdDisj,efac), forallMatching);
              if(u.implies(constr0,constr1)) {
                simplified = true;
                myprintf("before substitution\n");
                myprint(flaRel);
                Expr upd = replaceAll(flaRelRenamed, forallMatching);
                //Expr tmp = conjoin(updConj, efac);
                flaUpdDisj.insert(upd);
                transformed.insert(replaceAll(disjoin(flaUpdDisj, efac), renaming_inv));
              } else {
                myprintf("failed to fold: remaining constraints are inconsistent\n");
                transformed.insert(*b); // failed to fold
              }
            }
            else {
                     transformed.insert(*b); // failed to fold
            }
        } else {
          transformed.insert(*b);
        };
      };
      myprintf("step 4\n");
      //myprintdisj(flaOrigDisj);
      //myprintdisj(flaUpdDisj);
      myprintf("folded\n");
      myprintconj(transformed);
      myprintf("simplifying conjunction\n");
      transformed = simplify_conj(transformed);
      myprintf("simplified conjunction\n");
      if(simplified) {
        //fla = normalizeArithm(replaceAll(flaForall, flaForall->last(),
        //                                       mk<EQ>(flaOrig->left(), conjoin(transformed,efac))));
        add_definition(flaRel, conjoin(transformed, efac), usedNu);
        //printall();
        return true;
      } else return false;
    };

    bool iter_and()
    {
      SMTUtils u(efac);
      ExprSet flaOrigConj;
      Expr comm = fla;
      //getConj(flaOrig->right(), flaOrigConj);
      getConj(flaOrig, flaOrigConj);
      fla = normalizeArithm(fla);
      ExprSet flaApps;
      filter (fla, bind::IsFApp (), inserter(flaApps, flaApps.begin()));
      ExprMap allRepls;
      fla = flex_unfold(fla);
      fla = expandExists(fla);
      fla = simplifyExists(fla);
      fla = expandConjSubexpr(fla);
      usedNu = false;
      muVar = bind::boolConst(mkTerm<string> ("mu", efac));
      //fla = expandDisjSubexpr(fla);
      //myprint(fla);
      ExprSet flaUpdDisj;
      getDisj(fla, flaUpdDisj);
      myprintf("step 1\n");
      myprintconj(flaOrigConj);
      myprint(fla);

      ExprSet used;
      bool hasFapps = false;
      bool simplified = false;

      map <Expr, ExprVector> all;
      map <Expr, ExprVector> usedTmp;
      ExprSet transformed;
      ExprSet constrconj;
      for (auto it = flaOrigConj.begin(); it != flaOrigConj.end();)
      {
        if (!isOpX<FAPP>(*it))
          {
            constrconj.insert(*it);
            it = flaOrigConj.erase(it);
          }
        else ++it;
      }
      Expr constr = conjoin(constrconj,efac);
      for (auto b = flaUpdDisj.begin(); b!=flaUpdDisj.end();)
      {
        ExprMap forallMatching;
        bool foundall = true;
        //ExprSet usedOrig;
        ExprSet usedUpd{};
        ExprSet flaUpdConj;
        getConj(*b, flaUpdConj);
        for (auto it = flaOrigConj.begin(); it != flaOrigConj.end();)
        {
          if (!isOpX<FAPP>(*it))
          {
            return false;
          }
          hasFapps = true;
          ExprVector av;
          filter (*it, bind::IsConst (), inserter(av, av.begin()));
          Expr a = normalizeArithm(replaceAll(*it, forallMatching));
          //Expr a = normalizeArithm(*it);
          bool found = false;
          for (auto it2 = flaUpdConj.begin(); it2 != flaUpdConj.end();)
          {
            //myprintf("flaUpdDisj \n");
            //myprintdisj(flaUpdDisj);
            if (!isOpX<FAPP>(*it2))
            {
              ++it2;
              continue;
            }
            Expr d = normalizeArithm(*it2);
            ExprMap matching1;
            myprintf("comparing \n");
            myprint(a);
            myprintf("and \n");
            myprint(d);
            if (findMatchingSubexpr (a, d, av, matching1))
            {
              myprintf("matching found\n");
              int toCont = false;
              for (auto & m : matching1)
              {
                if (m.first != NULL && m.second != NULL)
                {
                  Expr tmp = replaceAll (m.second, forallMatching);
                  //Expr tmp = m.second;
                  if (forallMatching[m.first] != NULL &&
                      forallMatching[m.first] != tmp)
                  {
                    toCont = true;
                    break;
                  }
                  if (forallMatching[m.first] == NULL)
                  {
                    forallMatching[m.first] = m.second;
                  }
                }
              }
              if (toCont)
              {
                  myprintf("matching rejected\n");
                ++it2;
                continue;
              }

              usedUpd.insert(*it2);
              //used.insert(*it2);
              it2 = flaUpdConj.erase(it2);
              found = true;
              break;
            }
            ++it2;
          };
          //myprint(*it);
          ++it;
          if (!found )
            {foundall=false; break;};
          //else {
              //myprintf("!!!1\n");
            //usedOrig.insert(*it);
              //myprintf("!!!2\n");
          //};
        };
        Expr constrUpd = replaceAll(constr, forallMatching);
        if(foundall && u.implies(conjoin(flaUpdConj,efac),constrUpd)) {
          // sanity check of matching
          myprintf("sanity check\n");
          Expr tmp1 = conjoin(usedUpd, efac);
          myprint(tmp1);
          Expr tmp2 = replaceAll(conjoin(flaOrigConj,efac), forallMatching);
          myprint(tmp2);
            if(!u.isEquiv(tmp1, tmp2))
             return false;
          myprintf("matched\n");
          simplified = true;
          Expr upd = replaceAll(flaRel, forallMatching);
          flaUpdConj.insert(upd);
          Expr tmp = conjoin(flaUpdConj,efac);
          transformed.insert(tmp);
          //myprint(tmp);
          //myprintf("accumulated\n");
          //myprintconj(transformed);
        }
        else {
          myprintf("not matched\n");
          Expr tmp = *b;
          if(!u.implies(flex_unfold(tmp), mk<FALSE>(efac))) {
            transformed.insert(tmp);
          };
          myprint(tmp);
          myprintf("accumulated\n");
          myprintconj(transformed);
        };
        ++b;
      }
      myprintf("step 4\n");
      //myprintdisj(flaOrigDisj);
      //myprintdisj(flaUpdDisj);
      myprintf("folded\n");
      myprintdisj(transformed);
      transformed = simplify_disj(transformed);
      if(simplified) {
        //fla = normalizeArithm(replaceAll(flaForall, flaForall->last(),
        //                               mk<EQ>(flaOrig->left(), disjoin(transformed,efac))));
        add_definition(flaRel, disjoin(transformed, efac), false);
        //printall();
        return true;
      } else return false;
    };

    void concat(ExprVector v1, ExprVector v2, ExprVector& v3) {
      for(auto it = v1.begin(); it!=v1.end(); ++it) v3.push_back(*it);
      for(auto it = v2.begin(); it!=v2.end(); ++it) v3.push_back(*it);
    }




    bool disjoint_vec(ExprVector av, ExprVector bv)
    {
      for(auto it = av.begin(); it!=av.end(); ++it){
        for(auto it2 = bv.begin(); it2!=bv.end(); ++it2)
          if (*it == *it2) return false;
      }
      return true;
    }

    bool member_vec(Expr a, ExprVector av)
    {
      for(auto it = av.begin(); it!=av.end(); ++it){
          if (*it == a) return true;
      }
      return false;
    }
    bool solve_eqs(ExprEqs& eqs,ExprVector freevars0,ExprVector freevars,ExprVector exvars0,
                   ExprVector exvars, ExprMap& forallMatching)
    {
      ExprVector vars;
      concat(freevars0, exvars, vars);
      myprintvec(vars);
      for(auto it = eqs.begin(); it != eqs.end(); ++it) {
        bool b = true;
        ExprPair tmp=*it;
        myprintf("moving equation for \n");
        myprint_eq(tmp);
        ExprPair eq = moveterm(*it, vars, b); // x+a = b+y --> x-y = b-a
        myprint_eq(eq);
        if(b) {
          *it = eq;
        } else return false; // failed to move terms
      }
      // find equations of the form x=e, and register them in forallMatching
      for(auto it = eqs.begin(); it != eqs.end(); ) {
        Expr left = it->first;
        Expr right = normalizeArithm(it->second);
        myprintf("checking an equation for \n");
        myprint(left);
        if(bind::isIntConst(left)) {
          it = eqs.erase(it);
          if (forallMatching.find(left)!=forallMatching.end()) {
            if (forallMatching[left] != NULL && forallMatching[left] != right) {  // inconsistent substitutions
              myprintf("inconsistent substitutions found on\n");
              myprint(left);
              return false;
            }
          }
           myprintf("registering the equation\n");
          forallMatching[left] = right;
        } else ++it;
      };
      // try to solve the remaining equations (of the form a(x1,..xk) = e)
      //ExprMap tmpmap=forallMatching;
      myprintf("Solutions found so far\n");
      print_matching(forallMatching);
      bool b=true;
      for(auto it = eqs.begin(); it != eqs.end(); ){
        Expr left = replaceAll(it->first, forallMatching);
        Expr right = it->second;
        myprintf("solving an equation \n");
        myprint(left);
        myprintf("==\n");
        myprint(right);
        ExprPair ep = moveterm(make_pair(left,right), vars, b);
        myprintf("after moveterm:\n");
        myprint_eq(ep);
        left = normalizeArithm(ep.first);
        right = ep.second;
        ExprVector av;
        it = eqs.erase(it);
        filter (left, bind::IsConst (), inserter(av, av.begin()));
        if(av.empty()) { // there are no variables that can be instantiated; so the equation must be true
          if(!u.implies(mk<TRUE>(efac), mk<EQ>(left,right))){
            myprintf("here\n");
            return false;
          }
        } else {
          Expr x = av[0]; // pick a variable
          myprintf("picked the variable\n");
          myprint(x);
          av.erase(av.begin()+1, av.end());
          ExprPair neweq = moveterm(make_pair(left,right), av, b);
          if(!b) return false;
          myprintf("registering the substitution\n");
          Expr tmp1 = neweq.first;
          Expr tmp2 = neweq.second;
          myprintf("before normalization\n");
          myprint(tmp2);
          tmp2 = normalizeArithm(tmp2);
          myprint(tmp1);
          myprintf("-->\n");
          myprint(tmp2);
          register_newmap(forallMatching, tmp1, tmp2);
        }
      };
      //for (auto & m: tmpmap) {
      // f(m.first !=NULL && m.second !=NULL) {
      //  forallMatching[m.first] = m.second;
      //}
      //}
      // sanity check: free variables should not be mapped to terms that contain existential variables.
      myprintf("sanity checking for: \n");
      print_matching(forallMatching);
      myprintvec(freevars0);
      myprintf("existential\n");
      myprintvec(exvars0);
      for (auto & m: forallMatching) {
        if(m.first !=NULL && m.second !=NULL) {
          Expr x = m.first;
          Expr v = m.second;
          ExprVector bv;
          myprintf("forall matching\n");
          myprint(x);
          bool b = member_vec(x, freevars0);
          if(b) {
            filter(v, bind::IsConst(), inserter(bv, bv.begin()));
            myprintf("variables:\n");
            myprintvec(bv);
            if(!disjoint_vec(bv, exvars0)) return false;
          } else {myprintf("not a free variable\n");}
        }
      }        
      return true;
    }
    
    bool findMatchingSubexpr2(Expr pattern, Expr exp, ExprVector vars, ExprEqs& eqs)
    {
      pattern = normalizeArithm(pattern);
      exp = normalizeArithm(exp);
      if (pattern == exp && (isOpX<FDECL>(pattern) || isOpX<MPZ>(pattern)))  return true;
      if (bind::typeOf(pattern) != bind::typeOf(exp)) return false;

      if (isOpX<FAPP>(exp) && isOpX<FAPP>(pattern) && pattern->left() == exp->left()) {
        // for now, we consider only arithmetic expressions as the arguments of predicates
          for (int i = 1; i < pattern->arity(); i++) 
            {
              eqs.push_back(make_pair(pattern->arg(i),exp->arg(i)));
            };
        return true;
      };
      return false;
    }
    Expr foldexists(Expr e, Expr origRel, ExprSet origConj, Expr constr,
                    ExprEqs constreqs, ExprVector exvars, ExprVector exvars0,
                    ExprVector freevars, ExprVector freevars0, bool& found)
    {
      ExprSet conj;
      ExprSet transformed1;
      ExprVector vars;
      for (auto it = freevars0.begin(); it != freevars0.end(); ++it) {
          vars.push_back(*it);
      };
      for (auto it = exvars0.begin(); it != exvars0.end(); ++it) {
          vars.push_back(*it);
      };
      getConj(e, conj);
      for(auto it = conj.begin(); it != conj.end(); ++it) {
        // recursively apply foldexists
        Expr tmp = *it;
        if (isOpX<EXISTS>(tmp)) {
          ExprVector exvars1;
          for (int i = 0; i < tmp->arity() - 1; i++)
            exvars1.push_back(bind::fapp(tmp->arg(i)));
          Expr r = foldexists(tmp->last(), origRel, origConj, constr, constreqs, exvars1, exvars0, freevars, freevars0, found);
          //ExprVector args = tmp->args;
          //args[tmp->arity()-1] = r;
          tmp = simplifyExists(replaceAll(tmp, tmp->last(), r));
          // after simplification, conjunctions may occur at top-level
          ExprSet conjtmp;
          getConj(tmp, conjtmp);
          for (auto it1 = conjtmp.begin(); it1 != conjtmp.end(); ++it1) {
            transformed1.insert(*it1);
          }
        } else {
          transformed1.insert(tmp);
        }
      };
      myprintf("folding exists: second step\n");
      myprintconj(origConj);
      myprintconj(transformed1);
      ExprSet transformed2;
      for(auto it = transformed1.begin(); it != transformed1.end(); ++it) {
        Expr tmp = *it;
        ExprEqs eqs;
        ExprMap forallMatching;
        bool foundall = true;
        if (isOpX<EXISTS>(tmp)) {
          ExprVector exvars1;
          for (int i = 0; i < tmp->arity() - 1; i++)
            exvars1.push_back(bind::fapp(tmp->arg(i)));
          ExprSet updConj;
          getConj(tmp->last(), updConj);
          for (auto it1 = origConj.begin(); it1 != origConj.end();) {
            Expr a = normalizeArithm(replaceAll(*it1, forallMatching));
            bool foundlocal = false;
            for (auto it2 = updConj.begin(); it2 != updConj.end();) {
              if (!isOpX<FAPP>(*it2)) {
                ++it2;
              } else {
                Expr d = normalizeArithm(*it2);
                ExprMap matching1;
                if (findMatchingSubexpr2(a, d, vars, eqs)) {
                  myprintf("matching found\n");
                  it2 = updConj.erase(it2);
                  foundlocal = true;
                  break;
                };
                ++it2;
              };
            };
            ++it1;
            if(!foundlocal)
              {foundall = false; break;};
          };
          if(foundall) {
            myprintf("all matching found\n");
            myprint_eqs(eqs);
            myprintf("solving\n");
            print_matching(forallMatching);
            //forallMatching.clear();
            for (auto it = constreqs.begin(); it!=constreqs.end(); ++it) {
              eqs.push_back(*it);
            };
            bool r = solve_eqs(eqs,freevars0,freevars,exvars0,exvars1,forallMatching);
            myprint_eqs(eqs);
            if(r) {
              print_matching(forallMatching);
              Expr constr0 = replaceAll(constr, forallMatching);
              Expr constr1 = replaceAll(conjoin(updConj,efac), forallMatching);
              if(u.implies(constr1, constr0)) {
                found = true;
                myprintf("before substitution\n");
                myprint(origRel);
                Expr upd = replaceAll(origRel, forallMatching);
                updConj.insert(upd);
                //Expr tmp = conjoin(updConj, efac);
                transformed2.insert(upd);
                myprintf("folded formula\n");
                myprint(tmp);
                myprintf("-->\n");
                myprint(upd);
              } else {
                myprintf("failed to fold: remaining constraints are inconsistent\n");
                transformed2.insert(*it); // failed to fold
              }
            } else transformed2.insert(*it); // failed to fold
          } else {
            transformed2.insert(*it); // failed to fold
          }
        }
        else {
          transformed2.insert(*it);
        }
      }
      return conjoin(transformed2, efac);
    }

    bool iter_ex() 
    {
      SMTUtils u(efac);
      ExprSet flaOrigConj;
      //Expr flaO = flaOrig->right();
      Expr flaO = flaOrig;
      ExprVector exvars;
      myprintf("iter_ex is called\n");
      for (int i = 0; i < flaO->arity() - 1; i++)
         exvars.push_back(bind::fapp(flaO->arg(i)));
      ExprVector freevars;
      for (int i = 0; i < flaMain->arity() - 1; i++)
        // freevars <- free variables in the top goal;
        // this should be modified if we allow universal quantifiers
        // flaMain should be replaced with flaRel?
         freevars.push_back(bind::fapp(flaMain->arg(i)));
      //simplification of the original existential formula should be carried out before
      // iter_ex is called.
      //Expr fla0 = simpliftyExists(fla0); 
      Expr exbodyOrig = flaO->last();
      fla = normalizeArithm(fla);
      ExprSet flaApps;
      filter (fla, bind::IsFApp (), inserter(flaApps, flaApps.begin()));
      ExprMap allRepls;
      fla = flex_unfold(fla);
      fla = expandExists(fla);
      myprintf("expanded\n");
      myprint(fla);
      fla = simplifyExists(fla);
      myprintf("simplified\n");
      myprint(fla);
      myprintf("body of original formula\n");
      myprint(exbodyOrig);
      myprintf("with existentially quantified variables:\n");
      myprintvec(exvars);
      myprintf("and free variables:\n");
      myprintvec(freevars);
      myprintf("expanded formula\n");
      myprint(fla);
      ExprVector exvars0;
      ExprVector freevars0;
      ExprMap renaming;
      ExprMap renaming_inv;
      for (auto it = exvars.begin(); it != exvars.end();++it) {
        Expr tmp = *it;
        Expr tmp0 = cloneVar(tmp, mkTerm<std::string> (lexical_cast<string>(tmp)+"_tmp", efac));
        exvars0.push_back(tmp0);
        renaming[tmp] = tmp0;
        renaming_inv[tmp0] = tmp;
      };
      for (auto it = freevars.begin(); it != freevars.end();++it) {
        Expr tmp = *it;
        Expr tmp0 = cloneVar(tmp, mkTerm<std::string> (lexical_cast<string>(tmp)+"_tmp", efac));
        freevars0.push_back(tmp0);
        renaming[tmp] = tmp0;
        renaming_inv[tmp0] = tmp;
      };
      Expr exbodyOrigRenamed = replaceAll(exbodyOrig, renaming);
      Expr flaRelRenamed = replaceAll(flaRel, renaming);
      myprint(exbodyOrigRenamed);
      getConj(exbodyOrigRenamed, flaOrigConj);
      usedNu = false;
      muVar = bind::boolConst(mkTerm<string> ("mu", efac));
      //fla = expandDisjSubexpr(fla);
      //myprint(fla);
      ExprSet flaUpdDisj;
      getDisj(fla, flaUpdDisj);
      myprintf("step 1\n");
      myprintconj(flaOrigConj);
      myprint(fla);

      ExprSet used;
      bool hasFapps = false;
      bool simplified = false;

      map <Expr, ExprVector> all;
      map <Expr, ExprVector> usedTmp;
      ExprSet transformed;
      ExprSet constrconj;
      ExprEqs constreqs;
      for (auto it = flaOrigConj.begin(); it != flaOrigConj.end();)
      {
        if (!isOpX<FAPP>(*it))
          {
            Expr tmp = *it;
            constrconj.insert(tmp);
            if(isOpX<EQ>(tmp)){
              Expr left_orig = tmp->left();
              Expr right_orig = tmp->right();
              Expr left_upd = replaceAll(left_orig, renaming_inv);
              Expr right_upd = replaceAll(right_orig, renaming_inv);
              ExprPair tmp2 = make_pair(mk<PLUS>(left_orig,right_upd),
                                    mk<PLUS>(right_orig,left_upd));
              constreqs.push_back(tmp2);
              myprintf("saved equality information for\n");
              myprint(tmp);
              myprintf("saved equality\n");
              myprint_eqs(constreqs);
            }
            it = flaOrigConj.erase(it);
          }
        else ++it;
      }
      Expr constr = conjoin(constrconj,efac);
      bool found = false;
      for (auto b = flaUpdDisj.begin(); b!=flaUpdDisj.end();++b)
      {
        Expr tmp =
          replaceAll(foldexists(*b, flaRelRenamed, flaOrigConj, constr, constreqs, exvars, exvars0, freevars, freevars0, found), renaming_inv);
        transformed.insert(tmp);
      };
      if(!found) return false;
      myprintf("folded\n");
      myprintdisj(transformed);
      transformed = simplify_disj(transformed);
      if(found) {
        //fla = normalizeArithm(replaceAll(flaForall, flaForall->last(),
        //                               mk<EQ>(flaOrig->left(), disjoin(transformed,efac))));
        add_definition(flaRel, disjoin(transformed, efac), false);
        return true;
      } else return false;
    };
  
    bool iter2()
    {
      myprintf("parsed\n");
      flaOrig = simplifyExists(flaOrig);
      if (isOpX<OR>(flaOrig->right())) {
        myprintf("folding or\n");
        return iter_or();
      } else if (isOpX<AND>(flaOrig->right())) {
        myprintf("folding and\n");
        return iter_and();
      } else if (isOpX<EXISTS>(flaOrig->right())) {
        myprintf("folding ex\n");
          return iter_ex();
          //  return iter();
      } else return false;
    }

    ExprSet getFVars(Expr e)
    {
      //myprintf("computing free variables for\n");
      //myprint(e);
      ExprSet es;
      if(isOpX<OR>(e)){
        getDisj(e, es);
        return getFVars(es);
      } else if(isOpX<AND>(e)){
        getConj(e, es);
        return getFVars(es);
      } else if (isOpX<FORALL>(e) || isOpX<EXISTS>(e)) {
        es = getFVars(e->last());
        for (unsigned i=0; i< e->arity()-1; i++){
          //myprintf("erasing \n");
          Expr tmp = mk<FAPP>(e->arg(i));
          myprint(tmp);
          es.erase(tmp);
        }
      } else {
        filter(e, bind::IsConst (), inserter(es, es.begin()));
      };
      return es;
    }

    ExprSet getFVars(ExprSet es)
    {
      ExprSet vars;
      for(auto it = es.begin(); it!=es.end(); ++it) {
        ExprSet vars1 = getFVars(*it);
        for(auto it = vars1.begin(); it!=vars1.end(); ++it) {
            vars.insert(*it);
        }
      }
      return vars;
    }
    Expr fold_ex(Expr e, int iters)
    {
      myprintf("fold_ex is called\n");
      myprint(e);
      Expr body = e->last();
      body = fold_conj(body, iters);
      e = replaceAll(e, e->last(), body);
      myprintf("fold_ex:before simplifyExists\n");
      myprint(e);
      flaOrig = simplifyExists(e);
      myprintf("after simplifyExists\n");
      myprint(flaOrig);
      fla = flaOrig;
      myprint(flaOrig);
      ExprVector freevars;
      // Does this really compute the set of free variables??
      //filter(fla, bind::IsConst(), inserter(freevars, freevars.begin()));
      myprintf("computing free variables\n");
      ExprSet fvars = getFVars(fla);
      myprintf("free variables computed\n");
      myprintset(fvars);
      for(auto it = fvars.begin(); it!=fvars.end(); ++it) {
        freevars.push_back(*it);
      }
      Expr fvar = new_fvar(freevars);
      flaRel = bind::fapp(fvar, freevars);
      bool simplified=false;
      for (int i = 0; i < iters; i++) {
        simplified = iter_ex();
        if(simplified) break;
      };
      if(simplified) {
        fixVars.insert(fixVars.begin()+1, flaRel);
        return flaRel;
      } else {
        return flaOrig;
      }
    }

    Expr fold_conj(Expr e, int iters)
    {
      myprintf("fold_conj is called\n");
      myprint(e);
      ExprSet conj;
      e = simplifyExists(e);
      myprintf("simplified exists\n");
      myprint(e);
      getConj(e, conj);
      ExprSet conj2;
      for(auto it = conj.begin(); it!=conj.end(); ++it) {
        Expr tmp = *it;
        if(isOpX<EXISTS>(tmp)) {
          bool b1 = false;
          Expr e1 = fold_ex(*it, iters);
          conj2.insert(e1);
        }
        else
          conj2.insert(tmp);
      };
      ExprSet constr;
      // filter out non-applications
      for(auto it = conj2.begin(); it!=conj2.end(); ) {
        if(!isOpX<FAPP>(*it)) {
          constr.insert(*it);
          it = conj2.erase(it);
        }
        else ++it;
      }
      if (conj2.size()<2) {
        for(auto it = conj2.begin(); it!=conj2.end();++it ) {
          constr.insert(*it);
        };
        return conjoin(constr, efac);
      } else {        
        flaOrig = conjoin(conj2, efac);
        fla = flaOrig;
        myprintf("folding conjunction\n");
        myprint(flaOrig);
        ExprVector freevars;
        filter(fla, bind::IsConst(), inserter(freevars, freevars.begin()));
        Expr fvar = new_fvar(freevars);
        flaRel = bind::fapp(fvar, freevars);
        bool simplified=false;
        for (int i = 0; i < iters; i++) {
          simplified = iter_and();
          if(simplified) break;
        };
        if(simplified) {
          constr.insert(flaRel);
          fixVars.insert(fixVars.begin()+1, flaRel);
        } else {
          constr.insert(flaOrig);
        }
      };
      Expr tmp = conjoin(constr, efac);
      myprintf("exiting fold_conj\n");
      return conjoin(constr, efac);
    }

    Expr new_fvar(ExprVector vars)
    {
      ++name_id;
      string fname = "FIXV";
      fname = fname + std::to_string(name_id);
      ExprVector types;
      for (auto it = vars.begin(); it!=vars.end(); ++it) {
        types.push_back(bind::typeOf(*it));
      };
      types.push_back(mk<BOOL_TY>(efac));
      return bind::fdecl(mkTerm<std::string>(fname, efac), types);
    }
    Expr find_target_and_fold(Expr body, int iters)
    {
      body = expandExists(body);
      myprintf("find_target_and_fold: simplifying exists\n");
      myprint(body);
      body = simplifyExists(body);
      myprint(body);
      body = expandConjSubexpr(body);
      ExprSet disj;
      getDisj(body, disj);
      ExprSet disj2;
      for(auto it = disj.begin(); it!=disj.end(); ++it) {
        Expr e = fold_conj(*it, iters);
        disj2.insert(e);
      };
      ExprSet constr;
      // filter out non-applications
      for(auto it = disj2.begin(); it!=disj2.end(); ) {
        if(!isOpX<FAPP>(*it)) {
          constr.insert(*it);
          it = disj2.erase(it);
        }
        else ++it;
      }
      if (disj2.size()<2) {
        for(auto it = disj2.begin(); it!=disj2.end();++it ) {
          constr.insert(*it);
        };
        return disjoin(constr, efac);
      } else {        
        flaOrig = disjoin(disj2, efac);
        fla = flaOrig;
        ExprVector freevars;
        filter(fla, bind::IsConst(), inserter(freevars, freevars.begin()));
        Expr fvar = new_fvar(freevars);
        flaRel = bind::fapp(fvar, freevars);
        bool simplified=false;
        for (int i = 0; i < iters; i++) {
          usedNu = false;
          simplified = iter_or();
          if(simplified) break;
        };
        if(simplified) {
          constr.insert(flaRel);
          fixVars.insert(fixVars.begin()+1, flaRel);
        } else {
          constr.insert(flaOrig);
        }
      };
      return disjoin(constr, efac);
    }
    void tryfold (int iters)
    {
      /*
      system("glpsol -m lp.txt -o lp2.out");
      FILE * fp = fopen("lp2.out", "r");
      char str[256];
      string status = "Status:";
      string s = str;
      int n;
      while(s.compare(0,7,"Status:")!=0) {
        fscanf(fp, "%s", str);
        s = str;
      }
      fscanf(fp, "%s", str);
      s = str;
      if(s.compare(0,7,"INTEGER")!=0){
        printf("no solution\n"); return;
      };
      while(s.compare(0,6,"Column")!=0) {
        fscanf(fp, "%s", str);
        s = str;
      };
      while(s.compare(0,2,"x1")!=0) {
        fscanf(fp, "%s", str);
        s = str;
      };
      fscanf(fp, "%s%d", str, &n);
      printf("x1=%d\n",n);
      return;
      Expr zero = mkTerm(mpz_class(0), efac);
      Expr one = mkTerm(mpz_class(1), efac);
      Expr two = mkTerm(mpz_class(2), efac);
      Expr e0 = mk<MINUS>(zero,one);
      myprint(e0);
      Expr e1 = normalizeArithm(e0);
      myprint(e1);
      Expr e2 = mkVar("x");
      Expr e3 = mk<MINUS>(e0,e2);
      myprint(e3);
      Expr e4 = normalizeArithm(e3);
      myprint(e4);
      Expr e5 = mk<PLUS>(mk<MINUS>(mk<PLUS>(mkVar("r"), mk<MULT>(two, mkVar("z"))),one),mkVar("s2_tmp"));
      myprint(e5);
      Expr e6 = normalizeArithm(e5);
      myprint(e6);
      Expr e7 = mk<PLUS>(mk<MULT>(two, (mk<MINUS>(mkVar("z"),one))), two);
      myprint(e7);
      Expr e8 = normalizeArithm(e7);
      myprint(e8);
      Expr e9 = mk<MULT>(two, (mk<MINUS>(mkVar("z"),one)));
      myprint(e9);
      Expr e10 = normalizeArithm(e9);
      myprint(e10);
      ExprVector args;
      e0 = mk<UN_MINUS>(mkVar("y"));
      myprint(e0);
      e1 = mk<UN_MINUS>(mk<PLUS>(mkVar("s2_tmp"), mkVar("y")));
      myprint(e1);
      e2 = mk<UN_MINUS>(mk<PLUS>(mkVar("s3_tmp"), mkVar("v")));
      myprint(e2);
      e3 = mk<UN_MINUS>(mk<PLUS>(mkVar("s4_tmp"), mkVar("w")));
      myprint(e3);
      args.push_back(e1);
      args.push_back(e2);
      args.push_back(e3);
      e4 = mknary<PLUS>(args);
      myprint(e4);
      e5 = simplifyArithm(e4);
      myprint(e5);
      Expr e11 = mk<MINUS>(zero,mknary<PLUS>(args));
      myprint(e11);
      Expr e12 = simplifyArithm(e11);
      myprint(e12);
      //return;
      */
      Expr h = flaOrig->left();
      fla = nonrecDefs[h];
      fla = find_target_and_fold(fla, iters);
      nonrecDefs[h] = fla;
      printall();
      //flaRel = h;
      //myprintf("calling iter2\n");
      //myprint(flaOrig);
      //myprint(fla);
      // flaOrig: equation
      // flaRel: head
      // fla: body
    }
  };

  Expr swapExists (Expr e) 
  {
    if(!isOpX<EXISTS>(e)) return e;
    Expr body = e->last();
    if(!isOpX<EXISTS>(body)) return e;
    Expr body2 = body->last();
    //  e = (exists (x) (exists (y) body2))
    Expr body3 = replaceAll(e, body, body2);
    // body3 = (exists (x) body2)
    Expr body4 = simplifyExists(body3); // try to push "exists x" inside
    if(isOpX<EXISTS>(body4) && body4->first()==body3->first()) {
      return e; // give up swapping exists if "exists x" has not been pushed inside
    };
    return replaceAll(body, body2, body4);
  }

  inline static void mu (Expr s, int iters = 2)
  {
    MuSolver m(s->getFactory());
    m.initialize(s);
    m.tryfold(iters);
    //for (int i = 0; i < iters; i++) if (m.iter2()) break;
  }
}

#endif
