var arguments = process.argv.slice(2);
var script = null;
var fs = require('fs');
if(arguments.length == 1){
    console.log('read script from file '+arguments[0]);
    script = fs.readFileSync(arguments[0], 'utf8');
}
else{
    script='function a(a,b){ var a =\'abc\'; return a +b;}for(var i=0; i<10; i++) {var x=5+i;}; var a =[\'a\',\'b\',\'c\',[1,2]]; var b={a:2,b:1,c:{a:2,b:\'2\'}};a(1,2)';
    //script = 'function a(a,b){ var a =\'abc\'; return a +b;}for(var i=0; i<10; i++) {var x=5+i;}; var a =[\'a\',\'b\',\'c\',2,3];var b= {a:2,b:\'2\',c:{a:2}};'
}
var AST_Result=[];
var AST_Items=[];
AST_Result.push({tag:'Program_ROOT',value:0,parent:-1,id:-1});
var parentID=-1;
var currentID=-1;
var LargestID=0;

var esprima = require('esprima');
var escodegen = require('escodegen');
/* Codes from project ast-traverse */
var traverse = function (root, options) {
    "use strict";
    options = options || {};
    var pre = options.pre;
    var post = options.post;
    var skipProperty = options.skipProperty;
    
    function visit(node, parent, prop, idx) {
        if (!node || typeof node.type !== "string") {
            return;
        }
       
        var res = undefined;
        if (pre) {
            res = pre(node, parent, prop, idx);
        }
        
        if (res !== false) {
            for (var prop in node) {
                if (skipProperty ? skipProperty(prop, node) : prop[0] === "$") {
                    continue;
                }
                var child = node[prop];
                
                if (Array.isArray(child)) {
                    for (var i = 0; i < child.length; i++) {
                        
                        visit(child[i], node, prop, i);
                    }
                } else {
                    visit(child, node, prop,i);
                }
            }
        }
        
        if (post) {
            //console.log('post!!!!!');
            post(node, parent, prop, idx);
        }
    }
    
    visit(root, null);
};

//directly display parsing results
var ast = esprima.parse(script);

var result = JSON.stringify(ast, null, 2);
//console.log(result);


var CSPAutoGenVisitor = function(tree) {
    var ast = tree;
    var indent = 0;
    var id = 1;
    var string_count = 0;
    var number_count = 0;
    var boolean_count = 0;
    
    //helper methods
    //return value:
    //  atom: 'string', 'null', 'RegExp', 'number' and 'boolean'
    //  complex: 'array' and 'object'
    //  other: null and 'non-data-type'
    var get_node_value = function (node){
        if (!node || typeof node.type !== "string") {
            return null;
        }
        if (node.type === 'Literal') {

            return node.value;
        }
        else
            return 'null';
    }
    var get_data_node_type = function (node) {
        
        if (!node || typeof node.type !== "string") {
            return null;
        }
        //console.log(node.type);
        if (node.type === 'Literal') {
            
            var type = typeof node.value;
            if (type !== 'object'){
                return type;
            }
            else if(node.value instanceof RegExp){
                return 'RegExp';
            }
            else {
                return 'null';
            }
        }
        else if (node.type === 'ObjectExpression') {
            return 'object';
        }
        else if (node.type === 'ArrayExpression') {
            return 'array';
        }
        else {
            return 'non-data-type';
        }
    };
    
    var get_node_type = function (node){
        if (!node || typeof node.type !== "string") {
            return null;
        }

        if (node.type === 'Literal') {
            
            var type = typeof node.value;
            if (type !== 'object'){
                return type;
            }
            else if(node.value instanceof RegExp){
                return 'RegExp';
            }
            else {
                return 'null';
            }
        }
        else if (node.type === 'ObjectExpression') {
            return 'Object';
        }
        else if (node.type === 'ArrayExpression') {
            return 'Array';
        }

        else if(node.type ==='Identifier'){
            return 'ID'+node.name;
        }
        
        else if(node.type === 'BinaryExpression')
        {
            return 'BinOp';
        }
        else if(node.type ==='VariableDeclaration')
        {
            return 'VarDecl';
            
        }
        else if (node.type ==='VariableDeclarator')
        {
            //console.log(node.value+ "   "+ node   );
            return 'other';
        }
        else if (node.type === 'UpdateExpression')
        {
            //console.log(node.value+ "   "+ node   );
            return 'UnaryOp';
        }
        else if(node.type ==='EmptyStatement')//dont need this node.
        {
            return 'EmptyStatement';
        }
        else if(node.type =='BlockStatement')
        {
            return 'Block';
        }
        else if (node.type =='ForStatement')
        {
            return 'For';
        }
        else if(node.type =='FunctionDeclaration')
        {
            return 'FuncDecl';
        }
        else if (node.type ==='Program')
        {
            return 'other';
        }
        else if (node.type==='Property')
        {
            return 'other';
        }
        else if(node.type==='ReturnStatement')
        {
            return 'Return';
        }
        else if (node.type==='ExpressStatement')
        {
            return 'ExprStatement';
        }
        else if(node.type ==='CallExpression')
        {
            return 'FunctionCall';
        }
        else {
            return node.type;
        }
        
    }
    
    var convert_arr_to_non_nested_obj =
    function(arr, result, level) {
        console.log(arr)
        if (! arr['elements']) {
            console.warn("the array doesn't have elements");
            return result;
        }
        for (var index in arr['elements']){
            var elem = arr['elements'][index];
            if (!elem || typeof elem.type !== "string") {
                continue;
            }
           
            var type = get_data_node_type(elem);
            var sub_result = {};
            switch (type) {
                case 'boolean':
                    if (! result['CSP_Boolean']) {
                        result['CSP_Boolean'] = [elem.value];
                    }
                    else {
                        result['CSP_Boolean'].push(elem.value);
                    }
                    break;
                case 'string':
                    var label = 'CSP_String_'+level;
                    if (! result[label]) {
                        result[label] = [elem.value];
                    }
                    else {
                        result[label].push(elem.value);
                    }
                    break;
                case 'number':
                    //console.log("debug: "+elem.value);
                    if (!result['CSP_Number']) {
                        result['CSP_Number'] = [elem.value];
                    }
                    else {
                        result['CSP_Number'].push(elem.value);
                    }
                    break;
                case 'null':
                    if (! result['CSP_Null']) {
                        result['CSP_Null'] = [elem.value];
                    }
                    else {
                        result['CSP_Null'].push(elem.value);
                    }
                    break;
                case 'RegExp':
                    if (! result['CSP_RegExp']) {
                        result['CSP_RegExp'] = [elem.value];
                    }
                    else {
                        result['CSP_RegExp'].push(elem.value);
                    }
                    break;
                case 'object':
                    convert_obj_to_non_nested_obj(elem, sub_result, level+1);
                    combine_two_objs(result, sub_result);
                    break;
                case 'array':
                    convert_arr_to_non_nested_obj(elem, sub_result, level+1);
                    //console.log('subarray:'+sub_result);
                    combine_two_objs(result, sub_result);
                    break;
                case 'non-data-type':
                    if (! result['CSP_GAST']) {
                        result['CSP_GAST'] = [elem.type];
                    }
                    else {
                        result['CSP_GAST'].push(elem.type);
                    }
                    break;
                default:
                    console.warn('unknown elem for array '+type+' '+elem.type);
                    break;
            }
        }
    };
    var convert_obj_to_non_nested_obj =
    function(obj, result, level) {
        console.log(obj)
        if (! obj['properties']) {
            console.warn("the object doesn't have elements");
            return result;
        }
        for (var index in obj['properties']){
            var elem = obj['properties'][index];
            if (!elem || typeof elem.type !== "string") {
                continue;
            }
            
            var type = get_data_node_type(elem.value);
            console.log('value'+elem.value)
            var sub_result = {};
            switch (type) {
                case 'boolean':
                    if (! result['CSP_Boolean']) {
                        result['CSP_Boolean'] = [elem.value];
                    }
                    else {
                        result['CSP_Boolean'].push(elem.value);
                    }
                    break;
                case 'string':
                    var label = 'CSP_String_'+level;
                    if (! result[label]) {
                        result[label] = [elem.value];
                    }
                    else {
                        result[label].push(elem.value);
                    }
                    break;
                case 'number':
                    //console.log("debug: "+elem.value);
                    if (!result['CSP_Number']) {
                        result['CSP_Number'] = [elem.value];
                    }
                    else {
                        result['CSP_Number'].push(elem.value);
                    }
                    break;
                case 'null':
                    if (! result['CSP_Null']) {
                        result['CSP_Null'] = [elem.value];
                    }
                    else {
                        result['CSP_Null'].push(elem.value);
                    }
                    break;
                case 'RegExp':
                    if (! result['CSP_RegExp']) {
                        result['CSP_RegExp'] = [elem.value];
                    }
                    else {
                        result['CSP_RegExp'].push(elem.value);
                    }
                    break;
                case 'object':
                    convert_obj_to_non_nested_obj(elem, sub_result, level+1);
                    combine_two_objs(result, sub_result);
                    break;
                case 'array':
                    convert_arr_to_non_nested_obj(elem, sub_result, level+1);
                    //console.log('subarray:'+sub_result);
                    combine_two_objs(result, sub_result);
                    break;
                case 'non-data-type':
                    if (! result['CSP_GAST']) {
                        result['CSP_GAST'] = [elem.type];
                    }
                    else {
                        result['CSP_GAST'].push(elem.type);
                    }
                    break;
                default:
                    console.warn('unknown elem for array '+type+' '+elem.type);
                    break;
            }
        }
    };



    //assume the two params are non-nested
    var combine_two_objs =
    function (master_obj, elem_obj){
        for (var prop in elem_obj) {
            if (master_obj[prop]) {
                master_obj[prop] = master_obj[prop].concat(elem_obj[prop]);
            }
            else {
                master_obj[prop] = elem_obj[prop];
            }
        }
    };
    
    //visit methods
    var visit_hanlders = {};
    visit_hanlders.visitLiteral = function(node, parent, prop, idx){
        if (typeof node.value === 'string') {
            node.value = 'CSP_String';
            string_count++;
        }
        else if(typeof node.value === 'number') {
            node.value = 'CSP_Number';
            number_count++;
        }
        else if(typeof node.value === 'boolean') {
            node.value = 'CSP_Boolean';
            boolean_count++;
        }
        return true;
    };
    visit_hanlders.visitObjectExpression =
    function(node, parent, prop, idx,parentID) {
        var non_nested_obj = {};
        convert_obj_to_non_nested_obj(node,non_nested_obj,0);
        var count =0;
        /*
        for (var k in non_nested_obj) {
            console.log(Array(indent + 1).join(" ")+'object_elem: '+k+' val:'+non_nested_obj[k]);
            
            parentID=currentID;
            currentID=LargestID;
            LargestID=LargestID+1;
            
            AST_Result.push({tag:'object',value:non_nested_obj[k],parent:parentID,id:currentID});
            /*if(count==0){
             node.type='Array';
             node.value=[non_nested_obj[k]];
             }
             else{
             node.value.push(non_nested_obj[k]);
             }*/
            
        //}
        parentID =parentID
        
        return false;
    };
    visit_hanlders.visitArrayExpression =
    function(node, parent, indent,prop, idx,parentID) {
        var non_nested_obj = {};
        convert_arr_to_non_nested_obj(node,non_nested_obj,0);
        console.log(non_nested_obj)
        var count =0;
        for (var k in non_nested_obj) {
            
            console.log(Array(indent + 1).join(" ")+'array_elem: '+k+' val:'+non_nested_obj[k]);
            
            parentID=currentID;
            currentID=LargestID;
            LargestID=LargestID+1;

            AST_Result.push({tag:k+' array',value:non_nested_obj[k],parent:parentID,id:currentID});
            /*if(count==0){
            node.type='Array';
            node.value=[non_nested_obj[k]];
            }
            else{
                node.value.push(non_nested_obj[k]);
            }*/
            
        }
        parentID =parentID
        
        return false;
    };
    
    var visit = function(){
        traverse(ast, {
                 pre: function(node, parent, prop, idx) {


                 
                 var method = 'visit'+node.type;
                 var cont = true;
                 var tag =get_node_type(node);
                 var value = get_node_value(node);
                 if(tag!='other' && tag!='array' &&tag!='object'){
                
                 //node.type = tag;
                 //node.value = value;
                 //AST_Items.push({})
                if(getTag(currentID)==='FuncDecl' && tag==='Block'){
                
                
                 }
                 else{
                 console.log(Array(indent + 1).join(" ")+tag +' value:'+value);
                 parentID=currentID;
                 
                 currentID=LargestID;
                 LargestID=LargestID+1;
                       AST_Result.push({tag:tag,value:value,parent:parentID,id:currentID});
                 }
                 }
                 //console.log(Array(indent + 1).join(" ") + node.type +
                 //            ' value:'+node.value+' value type:'+get_data_node_type(node));
                 else if(tag=='array' ||tag =='object'){
                 console.log(method)
                 parentID=currentID;
                 
                 currentID=LargestID;
                 LargestID=LargestID+1;
                 AST_Result.push({tag:tag,value:value,parent:parentID,id:currentID});
                 
                 if (visit_hanlders.hasOwnProperty(method)) {
                 //console.log(Array(indent + 1).join(" ") + 
                 //  node.type +' value:'+node.value+' value type:');
                 //console.log('we found a property with method'+method);
                 //console.log(tag+'!!@@@!!!!')
                 
                 cont = visit_hanlders[method](node, parent, indent, prop, idx,parentID);
                 
                 }
                 }
                 indent += 2;
                 return cont;
                 },
                 
                 post: function(node) {
                 var tag =get_node_type(node);
                 //console.log('tag', tag);
                 if(tag!='other' && tag!='array' &&tag!='object'){
                // console.log('parentID', parentID);
                 currentID = parentID;
                // console.log('parentID = '+ parentID);
                 parentID = checkparentID(currentID);
                 
                 indent -= 2;
                 }
                 }
                 });
    }; //visit
    
    return {
        visit : visit
    };
};
var getTag = function(ID){
    for(var i =0;i<AST_Result.length;i++)
    {
        //console.log('in check parent id '+AST_Result[i].id + 'current ID '+currentID+'!!!!!');
        if(AST_Result[i].id===ID)
        {
            // console.log('after for in check parent id '+AST_Result[i].id + 'current ID '+currentID+'!!!!!');
            
            return AST_Result[i].tag;
        }
    }
    //if we can't find the parentID
    return null;
    console.log('error currentID: '+currentID+'\n');
}

var checkparentID=function(currentID){
    for(var i =0;i<AST_Result.length;i++)
    {
        //console.log('in check parent id '+AST_Result[i].id + 'current ID '+currentID+'!!!!!');
        if(AST_Result[i].id===currentID)
        {
           // console.log('after for in check parent id '+AST_Result[i].id + 'current ID '+currentID+'!!!!!');

            return AST_Result[i].parent;
        }
    }
    //if we can't find the parentID
    
    console.log('error currentID: '+currentID+'\n');
}

var visitor = CSPAutoGenVisitor(ast);
visitor.visit();

//generate new source codes
//var new_sc = escodegen.generate(ast);


console.log(AST_Result);


//var result = JSON.stringify(ast, null, 2);
//console.log(result);