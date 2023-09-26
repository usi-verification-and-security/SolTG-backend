#include <list>
#include <map>
#include <fstream>

using namespace std;

typedef struct {
  int chc_index;
  vector<int> srs;
  int ds;
} chc_structure_input;

typedef struct {
  int chc_index;
  vector<int> srs;
} chc_structure;

vector<int> entry_values;
map<int, vector<chc_structure>> ds_map_glob;

namespace deep {
  class node {
  public:
    int element;
    int chc_index;
    vector<node *> children;

    node(int theElement) {
      element = theElement;
      chc_index = -1;
    }

    node(int theElement, int theChc_value) {
      element = theElement;
      chc_index = theChc_value;
    }

    node(int theElement, node *p) {
      element = theElement;
    }

    node(int theElement, int theChc_value, vector<node *> c) {
      element = theElement;
      chc_index = theChc_value;
      for (int i = 0; i < c.size(); i++) {
        add_child(c[i]);
      }
    }

    node(int theElement, int theChc_value, vector<int> c) {
      element = theElement;
      chc_index = theChc_value;
      for (int i = 0; i < c.size(); i++) {
        node *n = new node{c[i]};
        add_child(n);
      }
    }

    void add_child(node *child) { children.push_back(child); }

    bool equals(node *n){
      if (children.size() != n->children.size()){
        return false;
      }else{
        if (element != n->element){return false;}
        bool tmp = true;
        for (int i = 0; i < children.size(); i++){
          tmp = children[i]->equals(n->children[i]);
          if (not tmp) {return false;}
        }
      }
      return true;
    }

    static node* clone(node* n){
      int tmp_e = n->element;
      int tmp_i = n->chc_index;
      vector<node *> new_chileds;
      for (auto c : n->children){
        new_chileds.push_back(clone(c));
      }
      node* out = new node{tmp_e, tmp_i, new_chileds};
      return out;
    }

    bool empty(){
      return children.empty();
    }
  };


  class chcTree {
  private:
    node *root;
    vector<node *> non_entry_leaves;
    int node_index;
  public:
    chcTree(int r){
      root = new node{r};
    }

    node* getRoot(){return root;}

    chcTree(node* r){
      root = r;
    }

    chcTree(int parent, int chc_index_value, chc_structure childrens){
      vector<node *> tmp_nodes;
      for (auto c : childrens.srs){
        auto tmp = new node{c};
        if (!contains_entry(c)){
          non_entry_leaves.push_back(tmp);
        }
        tmp_nodes.push_back(tmp);
      }
      root = new node{parent, chc_index_value, childrens.srs};
    }



    ~chcTree() {
      for (auto c: non_entry_leaves){
        delete c;
      }
      for(auto v: root->children){
        delete v;
      }
      delete root;

    }

    void deleteTree() {
      if (root == NULL) return;
      for(auto v: root->children){
        delete v;
      }
      free(root);
    }

    static chcTree* clone(chcTree *t){
      auto new_root = node::clone(t->root);
      auto n_leaves = find_all_non_entry_leaves(new_root); //ToDo: should be improved
      auto n_chcTree = new chcTree(new_root);
      n_chcTree->set_non_entry_leaves(n_leaves);
      return n_chcTree;
    }

    set<int> get_set(){
      set<int> out;
      out.insert(root->chc_index);
      for(auto e: root->children){
        get_set(out, *e);
      }
      return out;
    }

    vector<int> get_non_entry_leaves(){
      vector<int> tmp;
      for (auto n: non_entry_leaves){
        tmp.push_back(n->element);
      }
      return tmp;
    }

    void get_set(set<int> & out, node & n){
      out.insert(n.chc_index);
      for(auto  e: n.children){
        get_set(out, *e);
      }
    }

    void print_set(set<int> & s){
      for (auto e: s){
        outs() << e << " ";
      }
      outs() << endl;
    }

    void set_non_entry_leaves(vector<node*> l){
      non_entry_leaves = l;
    }

    static vector<node *> find_all_non_entry_leaves(node* n){ // ToDo: check again, maybe not the best solution
      vector<node *> tmp;
      if(n->children.empty() && !contains_entry(n->element)) {
        tmp.push_back(n);
        return tmp;
      }else{
        for (auto c: n->children){
          for (auto o: find_all_non_entry_leaves(c))
            tmp.push_back(o);
        }
        return tmp;
      }
    }

    const chcTree &operator=(chcTree &&rhs) {
      makeEmpty();
      root = std::move(rhs.root);
      rhs.root = nullptr;
      return *this;
    }

    bool empty() {
      return root->empty();
    }


    void printInOrder()  {
      if (empty()) {
        outs() << "tree is emtpy\n";
        return;
      }
      printInOrder(root);
      outs() << endl;
    }


    void printToDot(const char * filename, ufo::CHCs &ruleManager)  {
      if (empty()) {
        outs() << "tree is emtpy\n";
        return;
      }
      node_index = 0;
      std::ofstream fout(filename);
      fout << "digraph print {\n";
      dump_dot(fout, root, node_index, ruleManager);
      fout << "}\n";

    }

    void dump_dot(std::ofstream &fout, node *t, int parents_index, ufo::CHCs &ruleManager)  {
      if (t == nullptr) { return; }
      //fout << t->element << ":" << t->chc_index  << " ";
      if (t->element == -1) {
        fout << node_index << "[label=\"[-1]\" ordering=\"out\"]\n";
      }else{
        fout << node_index << "[label=\"" << ruleManager.chcs[t->chc_index].dstRelation  << "\" ordering=\"out\"]\n";
      }
      int p_index = node_index;
      for (int i = 0; i < t->children.size(); i++) {
        node_index++;
        fout << p_index << " -> " << node_index << "\n";
        dump_dot(fout, t->children[i], p_index, ruleManager);
      }
    }

    int numOfNodes() const {
      return numOfNodes(root);
    }

    int height() const {
      return height(root);
    }

    void makeEmpty() {
      makeEmpty(root); //? not sure
    }

    bool contains(const int &v) {
      return contains(v, root);
    }

    bool contains(const int &v, node *&t) {
      if (v == root->element) {
        return true;
      }
      return contains(v, root->children);
    }

    bool contains(const int &v, vector<node *> children) {
      //ToDo
      return false;
    }

    void printInOrder(node *t)  {
      if (t == nullptr) { return; }
      outs() << t->element << ":" << t->chc_index  << " ";
      for (int i = 0; i < t->children.size(); i++) {
        printInOrder(t->children[i]);
      }
    }

    void printLevelOrder(node *t) const {
      if (t == nullptr) { return; }
      list<node *> tmp_list;
      tmp_list.push_back(t);
      while (!tmp_list.empty()) {
        node *current = tmp_list.front();
        outs() << current->element << " ";
        for (int i = 0; i < t->children.size(); i++) {
          tmp_list.push_back(current->children[i]);
        }
        tmp_list.pop_front();
      }
    }

    void makeEmpty(node *&t) {
      if (t != nullptr) {
        for (int i = 0; i < t->children.size(); i++) {
          makeEmpty(t->children[i]);
        }
        delete t;
        t = nullptr;
      }
    }


    int numOfNodes(node *t) const {
      if (t == nullptr) { return 0; }
      int sum = 1;
      for (int i = 0; i < t->children.size(); i++) {
        sum += numOfNodes(t->children[i]);
      }
      return sum;
    }

    int height(node *t) const {
      if (t == nullptr) { return 0; }
      int max_h = 0;
      for (int i = 0; i < t->children.size(); i++) {
        int tmp = height(t->children[i]);
        if (max_h < tmp) {
          max_h = tmp;
        }
      }
      return 1 + max_h;
    }

    bool is_tree_full(){
      return non_entry_leaves.empty();
    }

    void print_map(){
      map<int, vector<chc_structure>>::iterator it;
      for (it = ds_map_glob.begin(); it != ds_map_glob.end(); it++){
        outs() << it->first;
        vector<chc_structure>::iterator it2;
        for (it2 = it->second.begin(); it2 != it->second.end(); it2++) {
          vector<int>::iterator it3;
          for (it3 = it2->srs.begin(); it3 != it2->srs.end(); it3++) {
            outs() << " " << *it3;
          }
          outs() << " chc_index: " << it2->chc_index;
        }
        outs() << endl;
      }
    }

    vector<vector<chc_structure>> get_all_permutations(){
      vector<vector<chc_structure>> oc;
      vector<chc_structure> out;
      for (int i = 0; i < non_entry_leaves.size(); i++){
        vector<int> tmp;
        chc_structure tmp_s = *new chc_structure{-1, tmp};
        out.push_back(tmp_s);
      }
      get_all_permutations(0, out, oc);
      return oc;
    }

    void get_all_permutations(int index, vector<chc_structure> &out,
                              vector<vector<chc_structure>> &out_collection){
      if (index >= non_entry_leaves.size()){
        vector<chc_structure> tmp;
        for (int i = 0; i < out.size(); i++) {
          //tmp.push_back(&out[i]);
          tmp.push_back(out[i]);
        }
        //out_collection.push_back(tmp);
        out_collection.push_back(tmp);
        return;
      }
      int el = non_entry_leaves[index]->element;
      int sz = ds_map_glob.find(el)->second.size();
      vector<chc_structure>::iterator it2;
      //for (int i = 0; i < sz; i++) {
      for (it2 = ds_map_glob.find(el)->second.begin(); it2 != ds_map_glob.find(el)->second.end(); it2++) {
        // update current out vector
        out[index] = *it2; //???
        get_all_permutations(index + 1, out, out_collection);
      }
    }

    static bool contains_entry(const int & elem){
      bool result = false;
      if(find(entry_values.begin(), entry_values.end(), elem) != entry_values.end() )
      {
        result = true;
      }
      return result;
    }

    void extend_non_entry_leaves(vector<chc_structure> new_mutations){
      vector<node *> new_non_entry_leaves;
      for (int i = 0; i < non_entry_leaves.size(); i++){
        auto new_mutation = new_mutations[i];
        vector<node *> tmp_node_list;
        for (auto nm: new_mutation.srs){
          auto n_tmp_node = new node{nm};
          if (!contains_entry(nm)){
            new_non_entry_leaves.push_back(n_tmp_node);
          }
          tmp_node_list.push_back(n_tmp_node);
        }
        non_entry_leaves[i]->children = tmp_node_list;
        non_entry_leaves[i]->chc_index = new_mutation.chc_index;
      }
      non_entry_leaves = new_non_entry_leaves;
    }


    void extend_by_terminals_nodes(map<int, node> &ds_term_node){
      for (auto n: non_entry_leaves){
        auto tmp = ds_term_node.find(n->element)->second;
        n->element = tmp.element;
        n->chc_index = tmp.chc_index;
        for(auto c: tmp.children){
          n->children.push_back(c);
        }
      }
    }

  };

  class chcTreeGenerator {

  public:
    vector<int> entry;
    int exit_v;
    int exit_index;
    vector<chc_structure_input> chc_int;
    vector<chcTree *> trees;
    //vector<chcTree *> fullTrees;
    map<int, vector<chc_structure>> ds_map;
    map<int, bool> ds_term; //store int value, which are terminals only (true) or cycle, branches (false)
    map<int, node> ds_term_node;

    chcTreeGenerator(vector<int> ep, int ex, int exit_index_value){
      entry = ep;
      exit_v = ex;
      exit_index = exit_index_value;
      entry_values = ep;
    }

    void clear(){
      entry = vector<int>();
      exit_v = -1;
      exit_index = -1;
      chc_int = vector<chc_structure_input>();
      trees = vector<chcTree *>();
      ds_map.clear();
      ds_term.clear();
      ds_term_node.clear();
      ds_map_glob.clear();
    }

    bool contains_entry(const int & elem){
      bool result = false;
      if( find(entry.begin(), entry.end(), elem) != entry.end() )
      {
        result = true;
      }
      return result;
    }

    bool isV_Equal(std::vector<int> &first, std::vector<int> &second)
    {
      if (first.size() != second.size()) {
        return false;
      }

      std::sort(first.begin(), first.end());
      std::sort(second.begin(), second.end());

      return first == second;
    }

    void add_chc_int(int chc_index, vector<int> srs_input, int dst_input){
      chc_structure_input tmp_s = *new chc_structure_input{chc_index, srs_input, dst_input};
      chc_int.push_back(tmp_s);
    }

    bool is_branch_or_cycle(int x, vector<int> &history){
      if (ds_term.find(x) != ds_term.end()){
        return ds_term.find(x)->second;
      }
      bool result = true;
      history.push_back(x);
      for (auto e: ds_map.find(x)->second[0].srs){
        if (e == -1){
          continue;
        }
        for (auto h: history){
          if (e == h){
            history.pop_back();
            return false;
          }
        }
        if (!is_branch_or_cycle(e, history)){
          history.pop_back();
          return false;
        }
      }
      history.pop_back();
      return true;
    }

    bool is_branch_or_cycle(int x){
      if (ds_term.find(x) != ds_term.end()){
        return ds_term.find(x)->second;
      }
      bool result = true;
      vector<int> history;
      history.push_back(x);
      for (auto e: ds_map.find(x)->second[0].srs){
        if (e == -1){
          continue;
        }
        if (!is_branch_or_cycle(e, history)){
          return false;
        }
      }
      return true;
    }

    void init_termination_tree(int x, node &n){
      if(ds_map.find(x) == ds_map.end()){
        assert(false);
      }
      for (auto e: ds_map.find(x)->second){
        n.chc_index = e.chc_index;
        for (int k: e.srs){
          if (k != -1){
            if (ds_term_node.find(k) != ds_term_node.end()){
              n.children.push_back(&ds_term_node.find(k)->second);
            } else {
              node tmp{k};
              init_termination_tree(k, tmp);
              n.children.push_back(&tmp);
            }
          }else{
            node *tmp = new node(-1,-1);
            n.children.push_back(tmp);
          }
        }
      }
    }



    void create_map(){
      for(auto chc: chc_int){
        if(ds_map.count(chc.ds) > 0){
          //should not happened
          chc_structure tmp_s = *new chc_structure{chc.chc_index, chc.srs};
          ds_map.find(chc.ds)->second.push_back(tmp_s);
          ds_map_glob.find(chc.ds)->second.push_back(tmp_s);
        }else{
          chc_structure tmp_s = *new chc_structure{chc.chc_index, chc.srs};
          vector<chc_structure> tmp{tmp_s};
          ds_map.insert({chc.ds, tmp});
          ds_map_glob.insert({chc.ds, tmp});

        }
      }
      //ds_map_glob = ds_map;
      //init ds_term
      map<int, vector<chc_structure>>::iterator it;
      for (it = ds_map.begin(); it != ds_map.end(); it++)
      {
        if (it->second.size() > 1){
          ds_term.insert({it->first, false});
        }
      }
      for (it = ds_map.begin(); it != ds_map.end(); it++)
      {
        if (ds_term.find(it->first) == ds_term.end()){
          ds_term.insert({it->first, is_branch_or_cycle(it->first)});
        }
      }
      //outs() << "ds_map: \n";
      map<int, bool>::iterator it2;
      for (it2 = ds_term.begin(); it2 != ds_term.end(); it2++)
      {
//        outs() << it2->first << " : " << it2->second << "\n";
      }

      for (it2 = ds_term.begin(); it2 != ds_term.end(); it2++)
      {
        if (it2->second){
          int id = it2->first;
          int chc_ind = ds_map.find(it2->first)->second[0].chc_index;
          node tmp{id, chc_ind};
          init_termination_tree(id, tmp);
          ds_term_node.insert({id, tmp});
        }
      }

    }

    void init_tree(){
      auto exit_points = ds_map.find(exit_v);
      for (auto items : exit_points->second){
        chcTree *t = new chcTree(exit_v, exit_index, items);
        //ToDo: check tree if it if "full" and  add to corresponding list
        trees.push_back(t);
      }
      //chcTree t = new chcTree
    }

    bool is_only_entries(vector<chc_structure> mutation) {
      for (int i = 0; i < mutation.size(); i++){
        for (int j = 0; j < mutation[i].srs.size(); j++){
          if (!contains_entry(mutation[i].srs[j])){
            return false;
          }
        }
      }
      return true;
    }

    bool is_future_terminals(vector<int> leaves) {
      for (auto l: leaves){
        if (!ds_term.find(l)->second)
          return false;
      }
      return true;
    }

    void print_trees(){
      outs() << "# of existing trees: " << trees.size() << " existing tree : " << endl;
      for (auto t: trees){
        t->printInOrder();
      }
    }

    void getNext(vector<chcTree *>  &complete_trees){
      vector<chcTree *> new_trees;
      for (int i = 0; i < trees.size(); i++){
        vector<vector<chc_structure>> all_permutations = trees[i]->get_all_permutations();
        for (auto ap : all_permutations){
          //clone tree
          auto nt = chcTree::clone(trees[i]);
          //add values from ap to tree
          nt->extend_non_entry_leaves(ap);
          if (is_future_terminals(nt->get_non_entry_leaves())){
            //outs() << "2\n";
            nt->extend_by_terminals_nodes(ds_term_node);
            complete_trees.push_back(nt);
            continue;
          }
          if (!is_only_entries(ap)) {
            // add tree to complete_trees
            new_trees.push_back(nt);
            //outs() << "1\n";
            continue;
          }
          //add tree to new_trees
          complete_trees.push_back(nt);

        }
      }
      for (auto t: trees){
        t->deleteTree();
      }
      trees = new_trees;
    }
  };

}
