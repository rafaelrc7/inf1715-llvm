#!/usr/bin/env lua
local lpeg = require "lpeg"

local pt = require "pt"

-----------------------------------------------------------
local function I (msg)
  return lpeg.P(function () print(msg); return true end)
end


local function throw (msg)
  io.stderr:write(msg, "\n")
  os.exit(false)
end


local intTy = {tag = "basictype", ty = "int"}
-----------------------------------------------------------

local parser

do

local function node (tag, ...)
  local labels = {...}
  return function (...)
    local values = {...}
    local t = {tag = tag}
    for i = 1, #labels do
      t[labels[i]] = values[i]
    end
    return t
  end
end


local function opL (term, op, tag)
  return lpeg.Cf(term * lpeg.Cg(op * term)^0,
                   node(tag, "e1", "op", "e2"))
end

local function binOpL (term, op)
  return opL(term, op, "binop")
end


local alpha = lpeg.R("az", "AZ", "__")
local digit = lpeg.R("09")
local alphanum = alpha + digit

local space = lpeg.V("space")

local opM = lpeg.C(lpeg.S("*/%")) * space
local opA = lpeg.C(lpeg.S("+-")) * space
local opC = lpeg.C(lpeg.P(">=") + "<=" + "==" + ">" + "<" + "~=") * space

local maxpos = 0

-- create a token
local function T (t)
  return t * space
end

local function Op (t)
  return lpeg.C(t) * space
end

local reserved = {}

-- create a reserved word
local function Rw (w)
  reserved[w] = true
  return w * -alphanum * space
end

local comment = "#" * (lpeg.P(1) - "\n")^0

local function checkID (_, _, id)
  return not reserved[id], id
end

local ID = lpeg.Cmt(lpeg.C(alpha * alphanum^0), checkID) * space

local numeral = lpeg.C(digit^1) / tonumber * space


local primary = lpeg.V("primary")
local power = lpeg.V("power")
local product = lpeg.V("product")
local sum = lpeg.V("sum")
local comparison = lpeg.V("comparison")
local conjunction = lpeg.V("conjunction")
local disjunction = lpeg.V("disjunction")
local stat = lpeg.V("stat")
local block = lpeg.V("block")
local call = lpeg.V("call")
local args = lpeg.V("args")
local params = lpeg.V("params")
local param = lpeg.V("param")
local funcDec = lpeg.V("funcDec")
local globalDec = lpeg.V("globalDec")
local retty = lpeg.V("retty")
local lhs = lpeg.V("lhs")
local ty = lpeg.V("ty")

local exp = disjunction

local grammar = lpeg.P{"prog",

  prog = space * lpeg.Ct((funcDec + globalDec)^1) * -1,

  globalDec = Rw"global" * ID * T":" * ty * T";"
                 / node("global", "name", "ty"),

  ty = Rw"int" * lpeg.Cc("int") / node("basictype", "ty")
     + Rw"array" * ty / node("array", "elem"),

  funcDec = Rw"func" * ID * T"(" * params * T")" * retty * (block + T";") /
                 node("func", "name", "params", "retty", "body"),

  retty = T":" * ty + lpeg.Cc(intTy),

  params = lpeg.Ct((param * (T"," * param)^0)^-1),

  param = ID * T":" * ty / node("param", "name", "ty"),

  block = T'{' * lpeg.Ct(stat^1) * T '}' / node("block", "body"),

  lhs = lpeg.Cf(ID / node("var", "id") * ( T"[" * exp * T"]")^0,
          node("indexed", "array", "index")),

  call = ID * T"(" * args * T")" / node("call", "name", "args"),

  args = lpeg.Ct((exp * (T"," * exp)^0)^-1),

  stat = T";"
       + block
       + T"@" * exp * T";" / node("print", "e")
       + Rw"local" * ID * T":" * ty * (T"=" * exp)^-1 * T";"
              / node("local", "name", "ty", "e")
       + Rw"while" * exp * block / node("while", "cond", "block")
       + Rw"if" * exp * block * (Rw"else" * block)^-1
              / node("if", "cond", "th", "el")
       + Rw"return" * exp * T";" / node("return", "e")
       + call
       + lhs * T"=" * exp * T";" / node("assg", "lhs", "exp"),

  primary = numeral / node("number", "val")
          + T"(" * exp * T")"
	  + Rw"newarray" * ty * T"[" * exp * T"]"
	         / node("newarray", "ty", "size")
	  + call
	  + lhs,

  power = T"-" * power / node("neg", "e")
        + T"~" * power / node("not", "e")
        + primary * (T"^" * power)^-1 /
	       function(e1, e2) return not e2 and e1 or
  		        {tag = "binop", op = "^", e1 = e1, e2 = e2} end,

  product = binOpL(power, opM),

  sum = binOpL(product, opA),

  comparison = opL(sum, opC, "comp"),

  conjunction = opL(comparison, Op"&&", "conj"),

  disjunction = opL(conjunction, Op"||", "disj"),

  space = (lpeg.S(" \t\n") + comment)^0
            * lpeg.P(function (_,p) maxpos = math.max(maxpos, p); return true end)
}

function parser (source)
  local ast = grammar:match(source)
  if not ast then
    io.stderr:write("syntax error: ",
       string.sub(source, maxpos - 20, maxpos - 1),
       "|", string.sub(source, maxpos, maxpos + 20))
    os.exit(1)
  end
  return ast
end

end
-----------------------------------------------------------
local Compiler = { funcs = {}, vars = {}, globals = {}, nvars = 0 }


function Compiler:newcount ()
  local count = self.count
  self.count = count + 1
  return count
end


local function count2reg (count)
  return string.format("%%T%d", count)
end


function Compiler:newreg ()
  return count2reg(self:newcount())
end


function Compiler:newlabel ()
  return string.format("L%d", self:newcount())
end

function Compiler:codeLabel (label)
  label = label or self:newlabel()
  self:emit("\n%s:\n", label)
  self.currentlabel = label
  return label
end


function Compiler:name2idx (name)
  local idx = self.vars[name]
  if not idx then
    idx = self.nvars + 1
    self.nvars = idx
    self.vars[name] = idx
  end
  return idx
end


function Compiler:preprocess (fmt)
  local lastdefined
  local regs = {}
  fmt = string.gsub(fmt, "%%r(%d) *(=?)", function(reg,def)
    if def == "=" then
      lastdefined = self:newreg()
      regs[reg] = lastdefined
    end
    return string.format("%%%s %s", regs[reg], def)
  end)
  return fmt, lastdefined
end


function Compiler:emit (fmt, ...)
  local fmt, res = self:preprocess(fmt)
  io.write(string.format(fmt, ...))
  return res
end


function Compiler:addJmp (label)
  self:emit("br label %%%s\n", label)
end


local function type2VM (ty)
  if ty.tag == "basictype" then
    if ty.ty == "int" then
      return "i32"
    end
  elseif ty.tag == "array" then
    return type2VM(ty.elem) .. "*"
  end
  error("unknown type" .. ty.tag)
end


local cmpop = {
  ["<"] = "slt",
  [">"] = "sgt",
  ["<="] = "sle",
  [">="] = "sge",
  ["=="] = "eq",
  ["~="] = "ne",
}


function Compiler:codeJmp (ast, labelT, labelF)
  local tag = ast.tag
  if tag == "not" then
    self:codeJmp(ast.e, labelF, labelT)
  elseif tag == "conj" then
    local label2 = self:newlabel()
    self:codeJmp(ast.e1, label2, labelF)
    self:codeLabel(label2)
    self:codeJmp(ast.e2, labelT, labelF)
  elseif tag == "disj" then
    local label2 = self:newlabel()
    self:codeJmp(ast.e1, labelT, label2)
    self:codeLabel(label2)
    self:codeJmp(ast.e2, labelT, labelF)
  elseif tag == "comp" then
    self:codeIntExp(ast.e1)
    self:codeIntExp(ast.e2)
    self:emit([[
%r1 = icmp %s %s %s, %s
br i1 %r1, label %%%s, label %%%s
]], cmpop[ast.op], type2VM(ast.e1.ty), ast.e1.res, ast.e2.res,
    labelT, labelF)
  else
    self:codeIntExp(ast)
    self:emit([[
%r1 = icmp eq i32 %s, 0
br i1 %r1, label %%%s, label %%%s
  ]], ast.res, labelF, labelT)
  end
end


function Compiler:searchVar (name)
  for i = #self.locals, 1, -1 do
    if self.locals[i].name == name then
      return self.locals[i]
    end
  end
  for i = 1, #self.params do
    if self.params[i].name == name then
      return self.params[i]
    end
  end

  if self.globals[name] then
    return self.globals[name]
  else
    throw("Variable '" .. name .. "' not found")
  end
end


local function typeEq (t1, t2)
  if t1.tag == t2.tag then
    if t1.tag == "basictype" then
      if t1.ty == t2.ty then return true end
    elseif t1.tag == "array" then
      return (typeEq(t1.elem, t2.elem))
    else error("unknown type " .. t1.tag)
    end
  end
  return false
end


function Compiler:codeAddr (array, index)
    local tyresVM = type2VM(array.ty.elem)
    return self:emit([[
%r1 = getelementptr %s, %s* %s, i32 %s
    ]], tyresVM, tyresVM, array.res, index.res)
end


function Compiler:codeLhs (ast)
  local tag = ast.tag
  if tag == "var" then
    local var = self:searchVar(ast.id)
    ast.res = var.idx
    return var.ty
  elseif tag == "indexed" then
    local tyarr = self:codeExp(ast.array)
    if tyarr.tag ~= "array" then
      throw("indexing a non array")
    end
    self:codeIntExp(ast.index)
    ast.res = self:codeAddr(ast.array, ast.index)
    return tyarr.elem
  else error("unknown tag " .. tag)
  end
end


function Compiler:codeCall (ast)
  local res = self:newreg()
  ast.res = res
  local func = self.funcs[ast.name]
  if not func then
    throw("calling undefined function: " .. ast.name)
  end
  if #func.params ~= #ast.args then
    throw("wrong number of arguments")
  end
  for i = 1, #ast.args do
    local arg = ast.args[i]
    local tyarg = self:codeExp(arg)
    if not typeEq(tyarg, func.params[i].ty) then
      throw("invalid parameter type " .. i)
    end
  end

  self:emit("%s = call %s @%s(",
             res, type2VM(func.retty), ast.name)

  for i = 1, #ast.args do
    local arg = ast.args[i]
    if i ~= 1 then self:emit(", ") end
    self:emit("%s %s", type2VM(arg.ty), arg.res)
  end
  self:emit(")\n")

  return func.retty
end


function Compiler:codePrint (ast)
  self:codeExp(ast.e)
  self:emit([[
call i32 (i8*, ...) @printf(i8* getelementptr ([4 x i8],
             [4 x i8]* @.%s, i64 0, i64 0), i32 %s)
]], (ast.e.ty == "array" and "str.1" or "str"), ast.e.res)
end


function Compiler:codeStat (ast)
  local tag = ast.tag
  if tag == "print" then
    self:codePrint(ast)
  elseif tag == "return" then
    local retty = self:codeExp(ast.e)
    if not typeEq(retty, self.retty) then
      throw("invalid return type")
    end
    self:emit("ret %s %s\n", type2VM(ast.e.ty), ast.e.res)
  elseif tag == "call" then
    self:codeCall(ast)
  elseif tag == "local" then
    local ety = ast.ty
    local lety = type2VM(ety)
    ast.idx = self:emit("%r1 = alloca %s\n", lety)
    if ast.e then
      self:codeExp(ast.e)
      if not typeEq(ety, ast.ty) then
        throw("incompatible types")
      end
      self:emit("store %s %s, %s* %s\n", lety, ast.e.res, lety, ast.idx)
    end
    self.locals[#self.locals + 1] = ast
  elseif tag == "while" then
    local Linit = self:newlabel()
    self:addJmp(Linit)
    self:codeLabel(Linit)
    local Lblock = self:newlabel()
    local Lend = self:newlabel()
    self:codeJmp(ast.cond, Lblock, Lend)
    self:codeLabel(Lblock)
    self:codeStat(ast.block)
    self:addJmp(Linit)
    self:codeLabel(Lend)
  elseif tag == "if" then
    local Lthen = self:newlabel()
    local Lelse = self:newlabel()
    self:codeJmp(ast.cond, Lthen, Lelse)
    self:codeLabel(Lthen)
    self:codeStat(ast.th)
    if not ast.el then
      self:addJmp(Lelse)
      self:codeLabel(Lelse)
    else
      local Lfinal = self:newlabel()
      self:addJmp(Lfinal)
      self:codeLabel(Lelse)
      self:codeStat(ast.el)
      self:addJmp(Lfinal)
      self:codeLabel(Lfinal)
    end
  elseif tag == "assg" then
    local tyrhs = self:codeExp(ast.exp)
    local tylhs = self:codeLhs(ast.lhs)
    if not typeEq(tyrhs, tylhs) then
      throw("invalid assignment")
    end
    self:emit("store %s %s, %s* %s\n",
                type2VM(tylhs), ast.exp.res, type2VM(tylhs), ast.lhs.res)
  elseif tag == "block" then
    local nvars = #self.locals
    for i = 1, #ast.body do
      self:codeStat(ast.body[i])
    end
    local diff = #self.locals - nvars
    for i = 1, diff do table.remove(self.locals) end
  else error("unknown tag " .. tag)
  end
end


function Compiler:codeIntExp (ast)
  local ty = self:codeExp(ast)
  if ty.tag ~= "basictype" or ty.ty ~= "int" then
    throw("expression not a number (" .. ast.tag .. ")")
  end
end

local ops = {["+"] = "add", ["-"] = "sub",
             ["*"] = "mul", ["/"] = "sdiv", ["%"] = "srem"
}

function Compiler:codeShortCircuit (ast, comp)
  self:codeIntExp(ast.e1)
  local label1 = self.currentlabel
  local labelelse = self:newlabel()
  local labelfinal = self:newlabel()
  self:emit([[
%r1 = icmp %s i32 %s, 0
br i1 %r1, label %%%s, label %%%s
]], comp, ast.e1.res, labelelse, labelfinal)
  self:codeLabel(labelelse)
  self:codeIntExp(ast.e2)
  local label2 = self.currentlabel
  self:emit("br label %%%s\n", labelfinal)
  self:codeLabel(labelfinal)
  ast.res = self:emit([[
%r1 = phi i32 [ %s, %%%s ], [ %s, %%%s ]
  ]], ast.e1.res, label1, ast.e2.res, label2)
end


function Compiler:codeExp (ast)
  local tag = ast.tag
  local ty
  if tag == "number" then
    ast.res = string.format("%d", ast.val)
    ty = intTy
  elseif tag == "var" then
    local var = self:searchVar(ast.id)
    ty = var.ty
    ast.res = self:emit("%r1 = load %s, %s* %s\n",
              type2VM(ty), type2VM(ty), var.idx)
  elseif tag == "indexed" then
    local aty = self:codeExp(ast.array)
    if aty.tag ~= "array" then
      throw("indexing a non array")
    end
    self:codeIntExp(ast.index)
    local regaddr = self:codeAddr(ast.array, ast.index)
    local tyresVM = type2VM(aty.elem)
    ast.res = self:emit([[
%r1 = load %s, %s* %s
    ]], tyresVM, tyresVM, regaddr)
    ty = aty.elem
  elseif tag == "newarray" then
    local tyelem = type2VM(ast.ty)
    local resizeI = self:emit([[
%r1 = getelementptr %s, %s* null, i32 1
%r2 = ptrtoint %s* %r1 to i64
]], type2VM(ast.ty), tyelem, tyelem)
    local rsize64 = self:newreg()
    local rsizeB = self:newreg()
    local pi8 = self:newreg()
    local pT = self:newreg()
    self:codeIntExp(ast.size)
    self:emit([[
%s = sext i32 %s to i64
%s = mul i64 %s, %s
%s = call i8* @malloc(i64 %s)
%s = bitcast i8* %s to %s*
]], rsize64, ast.size.res, rsizeB, rsize64,
    resizeI, pi8, rsizeB, pT, pi8, tyelem)
    ast.res = pT
    ty = {tag = "array", elem = ast.ty}
  elseif tag == "not" then
    self:codeIntExp(ast.e)
    ast.res = self:emit("%r1 = icmp eq i32 %s, 0\n%r2 = zext i1 %r1 to i32\n",
      ast.e.res)
    ty = intTy
  elseif tag == "neg" then
    local reg = self:newreg()
    ast.res = reg
    self:codeIntExp(ast.e)
    self:emit("%s = sub i32 0, %s\n", reg, ast.e.res)
    ty = intTy
  elseif tag == "comp" then
    self:codeExp(ast.e1)
    self:codeExp(ast.e2)
    ty = intTy
    ast.res = self:emit([[
%r1 = icmp %s %s %s, %s
%r2 = zext i1 %r1 to %s
]], cmpop[ast.op], type2VM(ast.e1.ty), ast.e1.res, ast.e2.res,
    type2VM(ast.e1.ty))
  elseif tag == "binop" then
    self:codeIntExp(ast.e1)
    self:codeIntExp(ast.e2)
    ty = intTy
    ast.res = self:emit("%r1 = %s i32 %s, %s\n",
                  ops[ast.op], ast.e1.res, ast.e2.res)
  elseif tag == "conj" then
    self:codeShortCircuit(ast, "ne")
    ty = intTy
  elseif tag == "disj" then
    self:codeShortCircuit(ast, "eq")
    ty = intTy
  elseif tag == "call" then
    ty = self:codeCall(ast)
  else error("unknown tag " .. tag)
  end
  ty = ty or {tag = "unknown"}
  ast.ty = ty
  return ty
end


function Compiler:codeFunc (ast)
  self.code = {}
  self.locals = {}
  self.params = ast.params
  self.retty = ast.retty
  self.count = 0
  local params = ""
  for i = 1, #self.params do
    local idx = self:newreg()
    self.params[i].idx = idx
    if i > 1 then params = params .. ", " end
    params = string.format("%s%s %s", params, type2VM(ast.params[i].ty), idx)
  end
  self:emit("define %s @%s (%s) {",
            type2VM(ast.retty), ast.name, params)
  self.funcs[ast.name] = { code = self.code, params = ast.params, retty = ast.retty }
  self:codeLabel()
  for i = 1, #self.params do
    local param = self.params[i]
    local addr = count2reg(self:newcount())
    local pty = type2VM(param.ty)
    self:emit("%s = alloca %s\n", addr, pty)
    self:emit("store %s %s, %s* %s\n", pty, param.idx, pty, addr)
    param.idx = addr
  end
  self:codeStat(ast.body)
  self:emit("ret i32 0\n")
  self:emit("}\n\n")
end


function Compiler:codeGlobal (ast)
  ast.idx = "@" .. ast.name
  self.globals[ast.name] = ast
  self:emit("@%s = global %s %s\n", ast.name, type2VM(ast.ty), codeZero(ast.ty))
end


function codeZero(ty)
  if ty.tag == "array" then
    return "null"
  elseif ty.tag == "basictype" then
    if ty.ty == "int" then
      return "0"
    end
  end

  throw("Unrecognised type: '" .. ty.tag .. "', '" .. ty.ty .. "'")
end


function compile (ast)
  Compiler:emit[[
declare i8* @malloc(i64)

@.str = private constant [4 x i8] c"%%d\0A\00"
@.str.1 = private constant [4 x i8] c"%%p\0A\00"
declare i32 @printf(i8*, ...)

]]
  for i = 1, #ast do
    local name = ast[i].name
    if Compiler.globals[name] or Compiler.funcs[name] then
      throw("Symbol '" .. name .. "' already defined.")
    end

    if ast[i].tag == "func" then
      Compiler:codeFunc(ast[i])
    elseif ast[i].tag == "global" then
      Compiler:codeGlobal(ast[i])
    else
      assert(0, "Invalid top level tag " .. ast[i].tag)
    end
  end
  local main = Compiler.funcs["main"]
  if not main then
    throw("no main function")
  end
  return main.code
end


-----------------------------------------------------------

local input = io.read("*a")
for i = 1, #arg do arg[arg[i]] = i end
local ast = parser(input)
if arg["-ast"] then print(pt.pt(ast)) end
local code = compile(ast)
if arg["-type"] then print(pt.pt(ast, true)) end

