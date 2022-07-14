#ifndef NONLINCHCSOLVER__HPP__
#define NONLINCHCSOLVER__HPP__

#include "HornNonlin.hpp"
#include "TGTree.hpp"

#include <fstream>
#include <chrono>
#include <queue>
#include <map>
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

      ExprVector tree_vars;
      ExprMap tree_map;
      ExprMap tree_vmap;

      map<string, map<string, vector<string>>> & signature; // <contract_name, <function_name_or_constructor, vector_of_param_names>>

  public:

      NonlinCHCsolver(CHCs &r, map<string, map<string,vector<string>>> & s) : m_efac(r.m_efac), ruleManager(r), u(m_efac), signature(s) {}

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

              outs () << " - ssa - - - - -\n";
              for(auto & s : ssaSteps){
                outs () << "    step: " << s << "\n";
              }
              if (u.isSat(ssaSteps)) // TODO: optimize with incremental SMT solving (i.e., using push / pop)
              {
                  Result_t res_tmp = solveIncrementally(bound, unr + 1, rels2, args2);
                  if (res_tmp == Result_t::SAT) return Result_t::SAT;           // bug is found for some combination
                  else if (res_tmp == Result_t::UNKNOWN) res = Result_t::UNKNOWN;
              }
          }
          return res;
      }

      // naive solving, without invariant generation
      void solveIncrementally(int bound = 3) {
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

    deep::chcTreeGenerator * initChcTree(){
      set<int> entries_tmp;
      set<int> src_set;
      set<int> dst_set;
      int exit_v = -1;
      for (int i  = 0; i < ruleManager.chcs.size(); i++){
        dst_set.insert(ruleManager.chcs[i].dstRelation->getId());
        if(ruleManager.chcs[i].isFact){
          auto entry = ruleManager.chcs[i].dstRelation->getId();
          //outs() << entry << endl;
          entries_tmp.insert(entry);
        }else{
          auto tmp_src = ruleManager.chcs[i].srcRelations;
          for (int j = 0; j < tmp_src.size(); j++){
            src_set.insert(tmp_src[j]->getId());
          }
        }
      }
      //find exit id
      set<int>::iterator itr;
      int exit_index = -1;
      int i = 0;
      for (itr = dst_set.begin();itr != dst_set.end(); itr++){
        if(src_set.find(*itr) == src_set.end() && entries_tmp.find(*itr) == entries_tmp.end()){
          exit_v = *itr;
        }
      }
      for (int i = 0; i < ruleManager.chcs.size(); i++){
        if(ruleManager.chcs[i].dstRelation->getId() == exit_v){
          exit_index = i;
          break;
        }
      }
      //outs() << "Exit index: " << exit_index << " : id" << exit_v << "\n";
      //vector<int> entries(entries_tmp.begin(), entries_tmp.end());
      vector<int> entries; //all leaves end with "-1", because sometimes node can be leaf (isFact=true) and not leaf
      entries.push_back(-1);
      for (int i  = 0; i < ruleManager.chcs.size(); i++) {
        auto tmp_src = ruleManager.chcs[i].srcRelations;
        for (int j = 0; j < tmp_src.size(); j++){
          if (dst_set.find(tmp_src[j]->getId()) == dst_set.end()){
            entries.push_back(tmp_src[j]->getId());
          }
        }
      }

      auto chcG = new deep::chcTreeGenerator{entries, exit_v, exit_index};
      for (int i  = 0; i < ruleManager.chcs.size(); i++) {
        if (!ruleManager.chcs[i].isFact) {
          auto tmp_src = ruleManager.chcs[i].srcRelations;
          vector<int> input_src;
          for (int j = 0; j < tmp_src.size(); j++){
            input_src.push_back(tmp_src[j]->getId());
          }
          chcG->add_chc_int(i, input_src, ruleManager.chcs[i].dstRelation->getId());
        }else{
          vector<int> input_src;
          input_src.push_back(-1);
          chcG->add_chc_int(i, input_src, ruleManager.chcs[i].dstRelation->getId());
        }
      }
      chcG->create_map();
      chcG->init_tree();
      return chcG;
    }

    ExprVector ssa;
    void treeToSMT(deep::node *t, int lev = 0, ExprVector srcVars = {})
    {
      if (t == nullptr || t->chc_index == -1) { return; }
      if (lev == 0) // should be the very first call
      {
        assert(srcVars.empty());
        ssa.clear();
      }

      auto & chc = ruleManager.chcs[t->chc_index];
      outs () << "\nssa-ing: ";
      ruleManager.print(chc);

      if (lev == 1)
        for (auto & i : chc.arg_inds)
        {
          tree_vars.push_back(srcVars[i]);
          tree_map[srcVars[i]] = chc.dstRelation;
          tree_vmap[srcVars[i]] = chc.arg_names[i];
          outs () << "   " << chc.dstVars[i] << " -> " << srcVars[i] << "\n";
        }

      auto body = chc.body;
      body = replaceAll(body, chc.dstVars, srcVars);
      ExprVector newLocs;
      for (auto & lv : chc.locVars)
      {
        Expr new_name = mkTerm<string>("_loc_" + to_string(varCnt++), m_efac);
        newLocs.push_back(cloneVar(lv, new_name));
      }
      body = replaceAll(body, chc.locVars, newLocs);

      if (t->children.size() == chc.srcVars.size())
      {
        for (int i = 0; i < t->children.size(); i++)
        {
          ExprVector vars;
          for (int j = 0; j < chc.srcVars[i].size(); j++)
          {
            Expr new_name = mkTerm<string>("_tg_" + to_string(varCnt++), m_efac);
            vars.push_back(cloneVar(chc.srcVars[i][j], new_name));
          }
          body = replaceAll(body, chc.srcVars[i], vars);
          treeToSMT(t->children[i], lev+1, vars);
        }
      }
      else
      {
        for (auto & c : t->children) assert(c->chc_index == -1);
      }
      //outs() << lev << ": " << t->chc_index  << ": " << body << "\n";
      ssa.push_back(body);
    }

    void printTree(deep::node *t, int lev = 0)
    {
      if (t == nullptr || t->chc_index == -1) { return; }

      auto & chc = ruleManager.chcs[t->chc_index];
      outs() << " chc: ";
      //pprint(chc.srcRelations);
      for(auto src: chc.srcRelations) {
        outs() << src << "(" << src->getId() << ")";
      }
      outs () << "   -> " << chc.dstRelation << "(" << chc.dstRelation->getId() << ")\n";
      if (t->children.size() == chc.srcVars.size())
      {
        for (int i = 0; i < t->children.size(); i++)
        {
          printTree(t->children[i], lev+1);
        }
      }
      else
      {
        for (auto & c : t->children) assert(c->chc_index == -1);
      }
    }


    void fillTodos(set<int> & todoCHCs)
    {
      // TODO: smarter
      // get points of control-flow divergence
      for (auto & d : ruleManager.decls) {
        vector<int> nums;
        for (int c = 0; c < ruleManager.chcs.size(); c++)
          if (ruleManager.chcs[c].dstRelation == d->left()) nums.push_back(c);

        if (nums.size() > 1)
          for (auto &o: nums) {
            string to_check = lexical_cast<string>(ruleManager.chcs[o].dstRelation);
            //todoCHCs.insert(o);
            if (to_check.find("NULL") == std::string::npos){ //to_check.find("summary_") == std::string::npos &&
              todoCHCs.insert(o);
            }
          }
      }

      // if the code is straight, just add queries
      if (todoCHCs.empty())
        for (int i = 0; i < ruleManager.chcs.size(); i++)
          if (ruleManager.chcs[i].isQuery)
            todoCHCs.insert(i);

      outs() << "TODOs : \n";
      for(auto tg: todoCHCs){
        outs() << tg << " : " <<  ruleManager.chcs[tg].dstRelation << "\n";
      }
    }


    // TODO: skeleton of the new implementation
    void exploreTracesNonLinearTG(int bnd)
    {
      set<int> todoCHCs;
      int number_of_tests = 0;

      fillTodos(todoCHCs);

      for (int cur_bnd = 1; cur_bnd <= bnd && !todoCHCs.empty(); cur_bnd++)
      {
        outs () << "new iter with cur_bnd = "<< cur_bnd <<"\n";
        ruleManager.mkNewQuery(cur_bnd);
        //ruleManager.print(ruleManager.chcs.back());
        //ruleManager.print_parse_results();
        //ruleManager.print();

        // 1. restart tree generation (up to some depth, e.g., 10)
        auto chcG = initChcTree();
        int tree_depth = 15;
        for (int depth = 1; depth <= tree_depth; depth++){
          // 2. enumerate all trees and call `isSat`
          vector<deep::chcTree *> trees;
          chcG->getNext(trees);
          //outs() << "trees size : " << trees.size() << "\n";
          for (auto t : trees){
            auto el = t->get_set();
            bool is_potential_tree_with_todo = false;
            for (int c : el) {
              if (find(todoCHCs.begin(), todoCHCs.end(), c) != todoCHCs.end()) {
                is_potential_tree_with_todo = true;
              }
            }
            if (!is_potential_tree_with_todo) {
              continue; //goto next tree, t doesn't contain todoCHCs
            }
            // clear Var vector and restart var counter ToDo: check
            tree_vars.clear();
            varCnt = 0;
            treeToSMT(t->getRoot());
            auto res = u.isSat(ssa);
            if (false == res) outs () << "unrolling unsat\n";
            else if (true == res) {
              outs () << "unrolling sat\n";
              printTree(t->getRoot(), 0);
              for (int c : el) {
                if (find(todoCHCs.begin(), todoCHCs.end(), c) != todoCHCs.end()) {
                  outs() << "FOUND: " << c << " # number_of_found_branches: " << number_of_tests <<"\n" ;
                  //outs() << "FOUND: " << ruleManager.chcs[c].dstRelation << "\n";
                  todoCHCs.erase(c); // remove CHCs from `todoCHCs`
                }
              }
              outs() << "ToDos: ";
              for (auto td: todoCHCs){
                outs() << td << " ";
              }
              outs() <<  "\n";
              Expr model = u.getModel();
              outs() << "MODEL : \n";
              //outs() << model << "\n";
              // find bnd-variables that were used in the SSA encoding of the tree
              // dump tree_var to the file;
              ofstream testfile;
              testfile.open ("testgen.txt", std::ios_base::app);
              testfile << "NEW TEST " << ++number_of_tests << "\n";
              for (auto vr: tree_vars){
                testfile << tree_map[vr] << " [" << tree_vmap[vr]
                         << "=" << u.getModel(vr) << "] \n";
              }
              testfile << "END TEST " << ++number_of_tests << "\n";
              testfile.close();

              // that correspond to inputs of functions

              if (todoCHCs.empty()){
                outs () << "ALL Branches are covered: DONE\n";
                return;
              }
            }
            else outs () << "unknown\n";
          }
          for (auto t : trees){
            t->deleteTree();
          }
        }
        chcG->clear();

        // GIVEN: at this point, there is only one query, and it is re-constructed in each iteration
        /* TODO:
          3. for all tree that gave `SAT`, extract tests, and remove CHCs from `todoCHCs`
        */

        ruleManager.chcs.pop_back(); // important: kill the query created in `mkNewQuery`
      }
    }

    void exploreTracesNonLinearTGOld(int cur_bnd, int bnd, bool skipTerm)
    {
      int number_of_found_branchs = 0;
      set<int> todoCHCs;
      auto chcG = initChcTree();

      //ToDo: find out how to get exit and entry values
      for (int i = 0; i < ruleManager.chcs.size(); i++)
        todoCHCs.insert(i);

      while (cur_bnd <= bnd && !todoCHCs.empty())
      {
        outs () << "new iter with cur_bnd = "<< cur_bnd <<"\n";
        vector<deep::chcTree *> trees;
        chcG->getNext(trees);
        if(trees.size() > 0){
          outs () << "MORE" <<"\n";
        }
        outs() << cur_bnd << endl;
        outs() << "# of terminals trees: " << trees.size() << " terminals tree: " << endl;

        for (auto t : trees){
          treeToSMT(t->getRoot());
          auto res = u.isSat(ssa);
          if (false == res) outs () << "unrolling unsat\n";
          else if (true == res) {
            //ToDo: What should be done here? How to generate data and remove from ToDos
            outs () << "unrolling sat\n";
            auto el = t->get_set();
            set<int> apps;
            for (int c : el) {
              if (find(todoCHCs.begin(), todoCHCs.end(), c) != todoCHCs.end()) {
                apps.insert(c);
                number_of_found_branchs++;
                outs() << "FOUND: " << c << " # number_of_found_branches: " << number_of_found_branchs <<"\n" ;
                todoCHCs.erase(c);
                for (int tmp_x : el) {
                  outs() << tmp_x << " ";
                }
                outs() <<  "\n";
                if (todoCHCs.empty()){
                  outs () << "ALL Branches are covered: DONE\n";
                  //exit(0);
                }
              }
            }
          }
          else outs () << "unknown\n";
        }
        cur_bnd++;
        continue;   // GF: skip for now

        chcG->print_trees();

        set<int> toErCHCs;
        for (auto & a : todoCHCs)
        {
          if (find(toErCHCs.begin(), toErCHCs.end(), a) != toErCHCs.end())
            continue;
          //vector<vector<int>> traces;
          //trace should be vector<chcTree *> traces
          //vector<deep::chcTree *> traces = chcG->getNext();

          //ToDo: update for Nonlinear
//                    getAllTracesTG(mk<TRUE>(m_efac), a, cur_bnd, vector<int>(), traces);
          outs () << "  exploring traces (" << trees.size() << ") of length "
                  << cur_bnd << ";       # of todos = " << todoCHCs.size() << "\n";
          /*         for (auto & b : todoCHCs)
                   {
                     outs () << b << ", ";
                   }
                   outs () << "\b\b)\n";*/

          int tot = 0;
          for (int trNum = 0; trNum < trees.size() && !todoCHCs.empty(); trNum++)
          {
            auto & tree = trees[trNum];
            auto t = tree->get_set();
            set<int> apps;
            for (int c : t) {
              if (find(todoCHCs.begin(), todoCHCs.end(), c) != todoCHCs.end() &&
                  find(toErCHCs.begin(), toErCHCs.end(), c) == toErCHCs.end()) {
                apps.insert(c);
                outs() << "FOUND: " << c << "\n" ;
              }
            }
            if (apps.empty()) continue;  // should not happen

            tot++;

//            auto & hr = ruleManager.chcs[t.back()];
//            //ToDo: update for Nonlinear
//            Expr lms;
//            for (int i = 0; i < hr.srcRelations.size(); i++) {
//              lms = invs[hr.srcRelations[i]];
//            }
////                        Expr lms = invs[hr.srcRelation];
//            if (lms != NULL && (bool)u.isFalse(mk<AND>(lms, hr.body)))
//            {
//              outs () << "\n    unreachable: " << t.back() << "\n";
//              toErCHCs.insert(t.back());
//              unreach_chcs.insert(t.back());
//              unsat_prefs.insert(t);
//              continue;
//            }
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
        for (auto t : trees){
          t->deleteTree();
        }

      }
      outs () << "Done with TG\n";
    }

//    inline void
//      solveNonlin(string smt, int inv) {
//          ExprFactory m_efac;
//          EZ3 z3(m_efac);
//          CHCs ruleManager(m_efac, z3);
//          ruleManager.parse(smt);
//          NonlinCHCsolver nonlin(ruleManager);
//
//          nonlin.solveIncrementally(inv);
//      };
  };

    inline void testgen(string smt, map<string, map<string, vector<string>>>& signature, unsigned maxAttempts, unsigned to,
                    bool freqs, bool aggp, bool enableDataLearning, bool doElim,
                    bool doDisj, int doProp, bool dAllMbp, bool dAddProp, bool dAddDat,
                    bool dStrenMbp, bool toSkip, int invMode, int lookahead,
                    bool lb, bool lmax, bool prio, int debug) {
      ExprFactory m_efac;
      EZ3 z3(m_efac);
      ExprMap invs;
      CHCs ruleManager(m_efac, z3);
      ruleManager.parse(smt, true);
      // ruleManager.print_parse_results();
      if (ruleManager.index_cycle_chc == -1 || ruleManager.index_fact_chc == -1){
        outs() << "no function found\n";
        return;
      }

      NonlinCHCsolver nonlin(ruleManager, signature);
      //nonlin.setSignature(signature);
      // nonlin.solveIncrementally();

      // if (nums.size() > 0)
      {
        // nonlin.initKeys(nums, lb);
        // nonlin.setInvs(invs);
        // todo
        nonlin.exploreTracesNonLinearTG(25);
      }
    }
};

#endif
