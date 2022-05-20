#ifndef NONLINCHCSOLVER__HPP__
#define NONLINCHCSOLVER__HPP__

#include "HornNonlin.hpp"

#include <fstream>
#include <chrono>
#include <queue>
// #include <stdlib.h>

using namespace std;
using namespace boost;

namespace ufo
{
  static void getCombinations(vector<vector<int>>& in, vector<vector<int>>& out, int pos = 0)
  {
    if (pos == 0) out.push_back(vector<int>());
    if (pos == in.size()) return;

    vector<vector<int>> out2;

    for (auto & a : in[pos])
    {
      for (auto & b : out)
      {
        out2.push_back(b);
        out2.back().push_back(a);
      }
    }
    out = out2;
    getCombinations(in, out, pos + 1);
  }

  enum class Result_t {SAT=0, UNSAT, UNKNOWN};
  struct KeyTG
  {
    int key;
    Expr eKey;
    vector<HornRuleExt*> rule;
    vector<int> locPos;
  };

  class NonlinCHCsolver {
  private:

      ExprFactory &m_efac;
      SMTUtils u;
      CHCs &ruleManager;
      int varCnt = 0;
      ExprVector ssaSteps;
      map <Expr, ExprSet> candidates;
      ExprMap invs;
      bool debug = false;

      map<int, Expr> eKeys;
      map<int, KeyTG*> mKeys;
      map<int, ExprVector> kVers;
      vector<map<int, ExprVector> > kVersVals;

      set<int> unreach_chcs;
      set<vector<int>> unsat_prefs;

  public:

      NonlinCHCsolver(CHCs &r) : m_efac(r.m_efac), ruleManager(r), u(m_efac) {}

      bool checkAllOver(bool checkQuery = false) {
          for (auto &hr: ruleManager.chcs) {
              if (hr.isQuery && !checkQuery) continue;
              if (!checkCHC(hr, candidates)) return false;
          }
          return true;
      }

      bool checkCHC(HornRuleExt &hr, map <Expr, ExprSet> &annotations) {
          ExprSet checkList;
          checkList.insert(hr.body);
          Expr rel;
          for (int i = 0; i < hr.srcRelations.size(); i++) {
              Expr rel = hr.srcRelations[i];
              ExprSet lms = annotations[rel];
              Expr overBody = replaceAll(conjoin(lms, m_efac), ruleManager.invVars[rel], hr.srcVars[i]);
              getConj(overBody, checkList);
          }
          if (!hr.isQuery) {
              rel = hr.dstRelation;
              ExprSet negged;
              ExprSet lms = annotations[rel];
              for (auto a: lms) negged.insert(mkNeg(replaceAll(a, ruleManager.invVars[rel], hr.dstVars)));
              checkList.insert(disjoin(negged, m_efac));
          }
          return bool(!u.isSat(checkList));
      }

      // naive solving, without invariant generation
      Result_t solveIncrementally(int bound, int unr, ExprVector &rels, vector <ExprVector> &args) {
          if (unr > bound)       // maximum bound reached
          {
              return Result_t::UNKNOWN;
          } else if (rels.empty()) // base case == init is reachable
          {
              return Result_t::SAT;
          }

          Result_t res = Result_t::UNSAT;

          // reserve copy;
          auto ssaStepsTmp = ssaSteps;
          int varCntTmp = varCnt;

          vector <vector<int>> applicableRules;
          for (int i = 0; i < rels.size(); i++) {
              vector<int> applicable;
              for (auto &r: ruleManager.incms[rels[i]]) {
                  Expr body = ruleManager.chcs[r].body; //ruleManager.getPostcondition(r);
                  if (args.size() != 0)
                      body = replaceAll(body, ruleManager.chcs[r].dstVars, args[i]);
                  // identifying applicable rules
                  if (u.isSat(body, conjoin(ssaSteps, m_efac))) {
                      applicable.push_back(r);
                  }
              }
              if (applicable.empty()) {
                  return Result_t::UNSAT;         // nothing is reachable; thus it is safe here
              }
              applicableRules.push_back(applicable);
          }

          vector <vector<int>> ruleCombinations;
          getCombinations(applicableRules, ruleCombinations);

          for (auto &c: ruleCombinations) {
              ssaSteps = ssaStepsTmp;
              varCnt = varCntTmp;
              ExprVector rels2;
              vector <ExprVector> args2;

              for (int i = 0; i < c.size(); i++) {
                  // clone all srcVars and rename in the body
                  auto &hr = ruleManager.chcs[c[i]];
                  Expr body = hr.body;
                  if (!hr.dstVars.empty()) body = replaceAll(body, hr.dstVars, args[i]);
                  vector <ExprVector> tmp;
                  for (int j = 0; j < hr.srcRelations.size(); j++) {
                      rels2.push_back(hr.srcRelations[j]);
                      ExprVector tmp1;
                      for (auto &a: hr.srcVars[j]) {
                          Expr new_name = mkTerm<string>("_fh_" + to_string(varCnt++), m_efac);
                          tmp1.push_back(cloneVar(a, new_name));
                      }
                      args2.push_back(tmp1);
                      body = replaceAll(body, hr.srcVars[j], tmp1);
                      for (auto &a: hr.locVars) {
                          Expr new_name = mkTerm<string>("_fh_" + to_string(varCnt++), m_efac);
                          body = replaceAll(body, a, cloneVar(a, new_name));
                      }
                  }

                  ssaSteps.push_back(body);
              }

              if (u.isSat(conjoin(ssaSteps,
                                  m_efac))) // TODO: optimize with incremental SMT solving (i.e., using push / pop)
              {
                  Result_t res_tmp = solveIncrementally(bound, unr + 1, rels2, args2);
                  if (res_tmp == Result_t::SAT) return Result_t::SAT;           // bug is found for some combination
                  else if (res_tmp == Result_t::UNKNOWN) res = Result_t::UNKNOWN;
              }
          }
          return res;
      }

      // naive solving, without invariant generation
      void solveIncrementally(int bound) {
          ExprVector query;
          query.push_back(ruleManager.failDecl);
          vector <ExprVector> empt;
          switch (solveIncrementally(bound, 0, query, empt)) {
              case Result_t::SAT:
                  outs() << "sat\n";
                  break;
              case Result_t::UNSAT:
                  outs() << "unsat\n";
                  break;
              case Result_t::UNKNOWN:
                  outs() << "unknown\n";
                  break;
          }
      }

      void setInvs(ExprMap& i) {invs = i;}

      void initKeys(set<int>& keys, bool toElim = false)
      {
        for (auto & k : keys)
        {
          KeyTG* ar = new KeyTG();
          ar->eKey = mkMPZ(k, m_efac);
          eKeys[k] = ar->eKey;
          mKeys[k] = ar;
        }

        for (auto & hr : ruleManager.chcs)
        {
          bool anyFound = toElim;
          for (auto it = eKeys.begin(); it != eKeys.end(); ++it)
          {
            Expr var = NULL;
                      outs()  << hr.body << "\n";
                      outs()  << hr.head << "\n";
                      for (int i = 0; i < hr.srcRelations.size(); i++) {
                          auto &a = hr.srcRelations[i];
                          outs()  << i << " : " << a << "\n";
                      }
                      outs()  << "dstRelation : "<< hr.dstRelation << "\n";

            getKeyVars(hr.body, (*it).second, var);
            if (var != NULL)
            {
              int varNum = getVarIndex(var, hr.locVars);
              anyFound = true;
              assert(varNum >= 0);

              mKeys[(*it).first]->eKey = (*it).second;
              mKeys[(*it).first]->rule.push_back(&hr);
              mKeys[(*it).first]->locPos.push_back(varNum);
            }
          }
          if (!anyFound)
          {
            // optim since we don't need to use loc vars there
            hr.body = eliminateQuantifiers(hr.body, hr.locVars);
          }
        }
        for (auto it = eKeys.begin(); it != eKeys.end(); ++it)
        {
          if (mKeys[(*it).first]->locPos.empty())
          {
            outs() << "Error: key " << (*it).second << " not found\n";
            //exit(1);
          }
        }
      }

    void exploreTracesNonLinearTG(int cur_bnd, int bnd, bool skipTerm)
    {
      set<int> todoCHCs;

      // first, get points of control-flow divergence
      for (auto & d : ruleManager.decls)
        if (ruleManager.outgs[d->left()].size() > 1)
          for (auto & o : ruleManager.outgs[d->left()])
            todoCHCs.insert(o);

      // if the code is straight, just add queries
      if (todoCHCs.empty())
        for (int i = 0; i < ruleManager.chcs.size(); i++)
          if (ruleManager.chcs[i].isQuery)
            todoCHCs.insert(i);


      while (cur_bnd <= bnd && !todoCHCs.empty())
      {
        outs () << "new iter with cur_bnd = "<< cur_bnd <<"\n";
        set<int> toErCHCs;
        for (auto & a : todoCHCs)
        {
          if (find(toErCHCs.begin(), toErCHCs.end(), a) != toErCHCs.end())
            continue;
          vector<vector<int>> traces;
          //ToDo: update for Nonlinear
//                    getAllTracesTG(mk<TRUE>(m_efac), a, cur_bnd, vector<int>(), traces);
          outs () << "  exploring traces (" << traces.size() << ") of length "
                  << cur_bnd << ";       # of todos = " << todoCHCs.size() << "\n";
          /*         for (auto & b : todoCHCs)
                   {
                     outs () << b << ", ";
                   }
                   outs () << "\b\b)\n";*/

          int tot = 0;
          for (int trNum = 0; trNum < traces.size() && !todoCHCs.empty(); trNum++)
          {
            auto & t = traces[trNum];
            set<int> apps;
            for (auto c : t)
              if (find(todoCHCs.begin(), todoCHCs.end(), c) != todoCHCs.end() &&
                  find(toErCHCs.begin(), toErCHCs.end(), c) == toErCHCs.end())
                apps.insert(c);
            if (apps.empty()) continue;  // should not happen

            tot++;

            auto & hr = ruleManager.chcs[t.back()];
            //ToDo: update for Nonlinear
            Expr lms;
            for (int i = 0; i < hr.srcRelations.size(); i++) {
              lms = invs[hr.srcRelations[i]];
            }
//                        Expr lms = invs[hr.srcRelation];
            if (lms != NULL && (bool)u.isFalse(mk<AND>(lms, hr.body)))
            {
              outs () << "\n    unreachable: " << t.back() << "\n";
              toErCHCs.insert(t.back());
              unreach_chcs.insert(t.back());
              unsat_prefs.insert(t);
              continue;
            }
//
//                        int suff = 1;
//                        bool suffFound = false;
//                        Expr ssa = toExpr(t);
//                        if (bool(!u.isSat(ssa)))
//                        {
//                            unsat_prefs.insert(t);
//                            continue;
//                        }
//                        else
//                        {
//                            if (hr.dstRelation == ruleManager.failDecl || skipTerm)
//                            {
//                                for ( auto & b : apps)
//                                    toErCHCs.insert(b);
//
//                                suffFound = true;
//                                if (getTest())
//                                {
//                                    printTest();
//
//                                    // try the lookahead method: to fix or remove
//                                    if (lookahead > 0)
//                                    {
//                                        Expr mdl = replaceAll(u.getModel(bindVars.back()), bindVars.back(), ruleManager.invVars[hr.dstRelation]);
//                                        outs () << "found: " << mdl << "\n";
//                                        letItRun(mdl, hr.dstRelation, todoCHCs, toErCHCs, lookahead, kVersVals.back());
//                                    }
//                                }
//                            }
//                            // default
//                        }
//
//                        while (!suffFound && suff < (bnd - cur_bnd))
//                        {
////              outs () << "     finding happy ending = " << suff;
//                            vector<vector<int>> tracesSuf;
//                            ruleManager.getAllTraces(hr.dstRelation, ruleManager.failDecl, suff++, vector<int>(), tracesSuf);
////              outs () << "    (" << tracesSuf.size() << ")\n";
//                            for (auto tr : tracesSuf)
//                            {
//                                tr.insert(tr.begin(), t.begin(), t.end());
//
//                                if (bool(u.isSat(toExpr(tr))))
//                                {
////                  outs () << "\n    visited: ";
//                                    for ( auto & b : apps)
//                                    {
//                                        toErCHCs.insert(b);
////                    outs () << b << ", ";
//                                    }
////                  outs () << "\b\n      SAT trace: true ";
////                  for (auto c : t) outs () << " -> " << *ruleManager.chcs[c].dstRelation;
////                  outs () << "\n       Model:\n";
//                                    suffFound = true;
//                                    if (getTest())
//                                        printTest();
//                                    break;
//                                }
//                            }
//                        }
          }
          outs () << "    -> actually explored:  " << tot << ", |unsat prefs| = " << unsat_prefs.size() << "\n";
        }
        for (auto a : toErCHCs) todoCHCs.erase(a);
        cur_bnd++;
      }
      outs () << "Done with TG\n";
    }

    inline void
      solveNonlin(string smt, int inv, int stren, bool maximal, const vector <string> &relsOrder, bool useGAS,
                  bool usesygus, bool useUC, bool newenc, bool fixCRels, string syguspath) {
          ExprFactory m_efac;
          EZ3 z3(m_efac);
          CHCs ruleManager(m_efac, z3);
          ruleManager.parse(smt);
          NonlinCHCsolver nonlin(ruleManager);

          nonlin.solveIncrementally(inv);
      };
  };

    inline void testgen(string smt, set<int>& nums, unsigned maxAttempts, unsigned to,
                    bool freqs, bool aggp, bool enableDataLearning, bool doElim,
                    bool doDisj, int doProp, bool dAllMbp, bool dAddProp, bool dAddDat,
                    bool dStrenMbp, bool toSkip, int invMode, int lookahead,
                    bool lb, bool lmax, bool prio, int debug) {
      ExprFactory m_efac;
      EZ3 z3(m_efac);
      ExprMap invs;
      CHCs ruleManager(m_efac, z3);
      ruleManager.parse(smt);
      NonlinCHCsolver nonlin(ruleManager);
      ruleManager.print();

      if (nums.size() > 0) {
        nonlin.initKeys(nums, lb);
        nonlin.setInvs(invs);
        // todo
        nonlin.exploreTracesNonLinearTG(1, 10, toSkip);
      }
    }
};

#endif
