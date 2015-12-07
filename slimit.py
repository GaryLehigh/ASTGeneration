from slimit.parser import Parser
from slimit.visitors import nodevisitor
#from ecmavisitor import ECMAVisitor
from slimit import ast
#from db_client import fetchScripts
#from utilities import deprecated
import itertools, sys, json, copy, hashlib, os,time

AST_Result=[]
parentID=-1
currentID=-1
largestID = -1



class ASTOutputNode():
  def __init__(self, tag):
    global largestID
    self.tag = tag
    self.value = None
    self.child_num = 0
    self.id =largestID
    largestID +=1
    self.parentID=-1
  def __eq__(self, other):
    if not isinstance(other, ASTOutputNode):
      return False
    return self.tag == other.tag

  def __ne__(self, other):
    return not self.__eq__(other)

class MyVisitor():
  def __init__(self, display=True):
    #only show class name and iterate children
    self.structure_class = set(["Block", "Node", \
      "FuncExpr", "FuncDecl", "This", "NewExpr", \
      ""])
    
    #leaf node and doesn't show value
    self.leaf_novalue_class = set(["Boolean", "Null", "Number", \
     "Regex"])

    #leaf node and show value
    self.leaf_value_class = set()

    self.node_order_list = []
    #initiate the tree with a root
    root = ASTOutputNode('Program_ROOT')
    self.node_order_list.append(root)
    
    self.display = display
    
    self.current_id_map = {}
    self.identifier_map = []
    self.first_level_seq = []
    self.scripts = []
    #self.root = tree
    #self.subtrees = []
    #self.string_value_list = []
  
  def is_structure_class(self, node):
    name = node.__class__.__name__
    if name in self.structure_class:
      return True
    return False 

  def is_leaf_novalue_class(self, node):
    name = node.__class__.__name__
    #print name
    if name in self.leaf_novalue_class:
      return True
    return False 
  
  def is_leaf_value_class(self, node):
    name = node.__class__.__name__
    
    if name in self.leaf_value_class:
      return True
    return False 

  def visit_sensitive_node(self, node, level,id):
    val = None
    if isinstance(node,ast.FunctionCall) or \
        isinstance(node, ast.NewExpr) or \
        isinstance(node, ast.ExprStatement):
        self.visit(node, level,id)
        val = "[FunctionCall||NewExpr]"
    elif isinstance(node, ast.Object):
      count = 0
      val = {}
      output_node = ASTOutputNode('Object')
      output_node.parentID=id
      self.node_order_list.append(output_node)
      for child in node:
        if isinstance(child, ast.Assign):
          
          key = self.visit_sensitive_node(child.left, level+1,output_node.id)
          value = self.visit_sensitive_node(child.right, level+1,output_node.id)
          print key
          print value
          
          if key != None and value != None:
            val[key] = value
        else:
            
          #print "    NO-ASSIGN-CHILD ",str(count),child, node
          if not "unknown" in val:
            val['unknown'] = child.__class__.__name__
          
          else:
            val['unknown'].append(child.__class__.__name__)

        count += 1
    elif isinstance(node, ast.Array):
        #print 'array'
      val = self.visit_Array(node, level,id)
    elif isinstance(node, ast.String):
        
      val = node.value
      print '12121212'+self.findtag(id)
      if(self.findtag(id)=='Object'):
        output_node = ASTOutputNode(node.__class__.__name__)
        output_node.value=val
        output_node.parentID = id
        self.node_order_list.append(output_node)

    elif isinstance(node, ast.Identifier):
      val = node.value
      print '12121212'+self.findtag(id)
      if(self.findtag(id)=='Object'):
        output_node = ASTOutputNode('ID'+val)
        output_node.value=None
        output_node.parentID = id
        self.node_order_list.append(output_node)
    else :#need more test to make everything the same
      val = node.value
      print '12121212'+self.findtag(id)
      if(self.findtag(id)=='Object'):
        output_node = ASTOutputNode(node.__class__.__name__)
        output_node.value=val
        output_node.parentID = id
        self.node_order_list.append(output_node)




    return val
  def findtag(self,id):
    for node in self.node_order_list:
      if node.id==id:
        return node.tag

  
  def visit_sensitive_children(self, node, level,id):
      #print node
    rs = []
    #print "DEBUG in processing visit_sensitive_children :NODE ",node
    for child in node:
    #print 'child'
      val = self.visit_sensitive_node(child, level+1,id)
    #print 'value' +str(val)
      if val != None and child.__class__.__name__!='Array':
        rs.append(val)
        output_node = ASTOutputNode(child.__class__.__name__)
        output_node.value=val
        output_node.parentID = id
        self.node_order_list.append(output_node)
    return rs
  
  def visit_Program(self, node, level,id):
      
      for child in node:
          tmp = self.visit(child, level,id)
      return None
  
  def visit_Object(self, node, level,id):
    #self.display = True
    space = ' '.ljust(level*2)
    tag =  node.__class__.__name__
    print 'taaaaaa'+tag
    if level == 0:
      self.current_id_map = {}
      index = len(self.node_order_list)

    if self.display:
      print "%s%s" %(space, tag)
    output_node = ASTOutputNode(tag)
    output_node.parentID=id
    self.node_order_list.append(output_node)
    no_child_len = len(self.node_order_list)
    #print "process object ",node
    val = {}
    for child in node:
      if isinstance(child, ast.Assign):
        key = self.visit_sensitive_node(child.left, level+1,output_node.id)
        value = self.visit_sensitive_node(child.right, level+1,output_node.id)
        if key != None and value != None:
          val[key] = value
      else:
        #print "    NO-ASSIGN-CHILD ",str(count),child, node
        if not "unknown" in val:
          val['unknown'] = child.__class__.__name__
        else:
          val['unknown'].append(child.__class__.__name__)

    output_node.value = None
    output_node.child_num = \
      len(self.node_order_list) - no_child_len
    if level == 0:
      self.identifier_map.append(self.current_id_map)
      self.first_level_seq.append(self.node_order_list[index:] )
    
      self.scripts.append(node.to_ecma())
    #if self.display:
    #  print "%s%d]" %(space, output_node.child_num)
    return val

  def visit_Array(self, node, level,id):
      
    space = ' '.ljust(level*2)
    tag =  node.__class__.__name__
    if self.display:
      print "%s%s" %(space, tag)
    #print "Array with %d child " % (len(node.items))
    if level == 0:
      self.current_id_map = {}
      index = len(self.node_order_list)
    
    output_node = ASTOutputNode(tag)
    output_node.parentID=id
    
    self.node_order_list.append(output_node)
    
    no_child_len = len(self.node_order_list)
    v = self.visit_sensitive_children(node, level+1,output_node.id)
    output_node.value = None
    output_node.child_num = \
      len(self.node_order_list) - no_child_len

    if level == 0:
      self.identifier_map.append(self.current_id_map)
      self.first_level_seq.append(self.node_order_list[index:])
      self.scripts.append(node.to_ecma())
    return output_node
    
  def visit_String(self, node, level,id):
    
    space = ' '.ljust(level*2)
    tag =  node.__class__.__name__
    output_node = ASTOutputNode(tag)
    output_node.parentID= id
    output_node.value = node.value
    output_node.child_num = 0
    self.node_order_list.append(output_node)
    #self.string_value_list.append(node.value)
    if self.display:
      print "%s%s [%s]" %(space, tag, node.value)
    return output_node.value
  
  def create_next_identifier(self):
    length = len(self.current_id_map)
    return "Var_%d" %length 

  def visit_Identifier(self, node, level,id):
    space = ' '.ljust(level*2)
    name = node.value
    if name in self.current_id_map:
      tag = self.current_id_map[name]
    else:
      tag = self.create_next_identifier()
      self.current_id_map[name] = tag

    tag = 'ID'+name
    output_node = ASTOutputNode(tag)
    output_node.parentID= id
    output_node.value = None
    output_node.child_num = 0
    self.node_order_list.append(output_node)
    #self.string_value_list.append(node.value)
    if self.display:
      print "%s%s" %(space, tag)
    return node.value

  def visit_FunctionCall(self, node, level,id):
    space = ' '.ljust(level*2)
    #tag = node.__class__.__name__ 
    tag = node.__class__.__name__ 
    if level == 0:
      self.current_id_map = {}
      index = len(self.node_order_list)
          
    output_node = ASTOutputNode(tag)
    output_node.parentID=id
    self.node_order_list.append(output_node)
    no_child_len = len(self.node_order_list)

    if self.display:
      print "%s%s" %(space, tag)
    #self.visit(node.identifier, level+1)
    rs = {'name':"FunCall", 'val':[]}
    for child in node:
      v = self.visit(child, level+1,id)
      if not v == None:
        rs['val'].append(v)
        
    output_node.child_num = \
      len(self.node_order_list) - no_child_len

    if level == 0:
      self.identifier_map.append(self.current_id_map)
      self.first_level_seq.append(self.node_order_list[index:])
      self.scripts.append(node.to_ecma())
    return rs

  def visit_VarStatement(self, node, level,id):
    for child in node:
      tmp = self.visit(child, level+1,id)
    return None



  def leaf_value_visit(self, node, level,id):
    global largestID
    space = ' '.ljust(level*2)
    tag = node.value
    output_node = ASTOutputNode(tag)
    output_node.parentID = id
    self.node_order_list.append(output_node)
    if self.display:
      print "%s%s" %(space, tag)
    output_node.child_num = 0
    return tag

  def leaf_novalue_visit(self, node, level,id):
    global largestID
    space = ' '.ljust(level*2)
    tag = node.__class__.__name__
    output_node = ASTOutputNode(tag)
    output_node.parentID=id
    
  
    
    #print tag
    output_node.value = node.value
    output_node.child_num = 0
    self.node_order_list.append(output_node)

    if self.display:
      print "%s%s" %(space, tag) +" "+output_node.value
    return tag

  def generic_visit(self, node, level, output_node_ID):
    global largestID
    space = ' '.ljust(level*2)
    tag = node.__class__.__name__
    if level == 0:
      self.current_id_map = {}
      index = len(self.node_order_list)
          #print 'level ==0'
    output_node = ASTOutputNode(tag)
    #print tag+ 'in level '+ str(level)+ '   parentid'+ str(output_node_ID)
    if level!=0:
        output_node.parentID=output_node_ID
        #print output_node_ID
       
        currentID = output_node.id
        parentID  = output_node.parentID
    
    self.node_order_list.append(output_node)
    no_child_len = len(self.node_order_list)
    
    
    if self.display:
      print "%s%s" %(space, tag)
    rs = {'name':tag, 'val': []}
    for child in node:
        #parentId should be passed to the lower level
      v = self.visit(child, level+1,output_node.id)
      
      #child_num += tmp
      if not v == None:
        rs['val'].append(v)
    #v = '_'.join(rs)
    output_node.child_num = \
      len(self.node_order_list) - no_child_len
    if level == 0:
      #print "LEVEL0:",self.root.__class__.__name__
      self.identifier_map.append(self.current_id_map)
      self.first_level_seq.append(self.node_order_list[index:])
      self.scripts.append(node.to_ecma())
    return rs
  
  def visit(self, node, level, output_node_ID):
    
    if self.is_leaf_novalue_class(node):
      self.leaf_novalue_visit(node,level,output_node_ID)
      return

    if self.is_leaf_value_class(node):
      self.leaf_value_visit(node,level,output_node_ID)
      return
      
    method = 'visit_%s' % node.__class__.__name__
    return getattr(self, method, self.generic_visit)(node, level,output_node_ID)

def analyzeJSCodes(script, display=False):
    try:
        parser = Parser()
        tree = parser.parse(script)
        visitor = MyVisitor(display)
        rs =visitor.visit(tree, 0,-1)
        #print rs
        #print "first_level_seq: %d" %len(visitor.first_level_seq)
        return visitor.node_order_list
    except Exception as e:
            print >>sys.stderr, "error parsing script: "+str(e)+" || "+script
            return None

##############TEST############

def main():
    #scripts = "for (var i=0; i<10; i++) { var x = {'a':i,'b':'AAAAA'}; " +\
    #          "var b = [{'a':1},{'b':'WW'}]} \n "+\
    #          "ma(123,'ddf'); ma('fff')"
    
    #compare scripts in a file
    scripts = 'function a(a,b){ var a =\'abc\'; return a +b;}for(var i=0; i<10; i++) {var x=5+i;}; var a =[\'a\',\'b\',\'c\',[1,2]]; var b={a:2,b:1,c:{a:2,b:\'2\'}};a(1,2)'
#scripts =

    vl = analyzeJSCodes(scripts, True)
    print '\n'
    
    for item in vl:
        print str(item.tag)+' '+str(item.value)+' '+' parentID: '+str(item.parentID)+'   id: '+str(item.id)


if __name__=="__main__":
    main()