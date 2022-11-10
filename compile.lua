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


local floatTy = {tag = "basictype", ty = "float"}
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

  globalDec = Rw"global" * ID * ty / node("global", "name", "ty"),

  ty = Rw"float" * lpeg.Cc("float") / node("basictype", "ty")
     + Rw"array" * ty / node("array", "elem"),

  funcDec = Rw"func" * ID * T"(" * params * T")" * retty * block /
              node("func", "name", "params", "retty", "body"),

  retty = T":" * ty + lpeg.Cc(floatTy),

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

  comparison = binOpL(sum, opC),

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
local Compiler = { funcs = {}, vars = {}, nvars = 0 }


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


function Compiler:name2idx (name)
  local idx = self.vars[name]
  if not idx then
    idx = self.nvars + 1
    self.nvars = idx
    self.vars[name] = idx
  end
  return idx
end

function Compiler:addCode (...)
  local params = {...}
  local code = self.code
  for i = 1, #params do
    code[#code + 1] = params[i]
  end
end


function Compiler:emit (fmt, ...)
  io.write(string.format(fmt, ...))
end


local function newlabel ()
  return {}
end


function Compiler:addJmp (jmp, label)
  self:addCode(jmp)
  self:addCode(0)
  label[#label + 1] = #self.code
end

function Compiler:fixlabel2target (label, target)
  for _, jmp in ipairs(label) do
    self.code[jmp] = target - jmp
  end
end

function Compiler:fixlabel2here (label)
  self:fixlabel2target(label, #self.code)
end


function Compiler:codeJmpFalse (ast, label)
  local tag = ast.tag
  if tag == "not" then
    self:codeJmpTrue(ast.e, label)
  elseif tag == "conj" then
    self:codeJmpFalse(ast.e1, label)
    self:codeJmpFalse(ast.e2, label)
  elseif tag == "disj" then
    local labelEnd = newlabel()
    self:codeJmpTrue(ast.e1, labelEnd)
    self:codeJmpFalse(ast.e2, label)
    self:fixlabel2here(labelEnd)
  else
    self:codeFloatExp(ast)
    self:addJmp("IfZJmp", label)
  end
end


function Compiler:codeJmpTrue (ast, label)
  local tag = ast.tag
  if tag == "not" then
    self:codeJmpFalse(ast.e, label)
  elseif tag == "disj" then
    self:codeJmpTrue(ast.e1, label)
    self:codeJmpTrue(ast.e2, label)
  elseif tag == "conj" then
    local labelEnd = newlabel()
    self:codeJmpFalse(ast.e1, labelEnd)
    self:codeJmpTrue(ast.e2, label)
    self:fixlabel2here(labelEnd)
  else
    self:codeFloatExp(ast)
    self:addJmp("IfNZJmp", label)
  end
end


function Compiler:searchLocal (name)
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
  return nil
end


local function type2VM (ty)
  if ty.tag == "basictype" then
    if ty.ty == "float" then
      return "double"
    end
  elseif ty.tag == "array" then
    return type2VM(ty.elem) .. "*"
  end
  error("unknown type" .. ty.tag)
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

function Compiler:codeLhs (ast)
  local tag = ast.tag
  if tag == "var" then
    local loc = self:searchLocal(ast.id)
    if not loc then
      self:addCode("storeG", self:name2idx(ast.id))
    else
      self:addCode("storeL", loc.idx)
      return loc.ty
    end
  elseif tag == "indexed" then
    local tyarr = self:codeExp(ast.array)
    if tyarr.tag ~= "array" then
      throw("indexing a non array")
    end
    self:codeFloatExp(ast.index)
    self:addCode("setarray")
    return tyarr.elem
  else error("unknown tag " .. tag)
  end
end


function Compiler:codeCall (ast)
  local func = self.funcs[ast.name]
  if not func then
    throw("calling undefined function: " .. ast.name)
  end
  if #func.params ~= #ast.args then
    throw("wrong number of arguments")
  end
  for i = 1, #ast.args do
    local tyarg = self:codeExp(ast.args[i])
    if not typeEq(tyarg, func.params[i].ty) then
      throw("invalid parameter type " .. i)
    end
  end
  self:addCode("call", func.code)
  return func.retty
end


function Compiler:codeStat (ast)
  local tag = ast.tag
  if tag == "print" then
    self:codeExp(ast.e)
    self:addCode("print")
  elseif tag == "return" then
    local retty = self:codeExp(ast.e)
    if not typeEq(retty, self.retty) then
      throw("invalid return type")
    end
    self:addCode("ret", #self.params)
    self:emit("ret %s %s\n", type2VM(ast.e.ty), ast.e.res)
  elseif tag == "call" then
    self:codeCall(ast)
    self:addCode("pop", 1)
  elseif tag == "local" then
    if not ast.e then
      self:addCode("push", 0)
    else
      self:codeExp(ast.e)
    end
    if ast.e and not typeEq(ast.e.ty, ast.ty) then
      throw("incompatible types")
    end
    self.locals[#self.locals + 1] = ast
    ast.idx = #self.locals
  elseif tag == "while" then
    local target = #self.code
    local L1 = newlabel()
    self:codeJmpFalse(ast.cond, L1)
    self:codeStat(ast.block)
    local L2 = newlabel()
    self:addJmp("jmp", L2)
    self:fixlabel2here(L1)
    self:fixlabel2target(L2, target)
  elseif tag == "if" then
    local L1 = newlabel()
    self:codeJmpFalse(ast.cond, L1)
    self:codeStat(ast.th)
    if not ast.el then
      self:fixlabel2here(L1)
    else
      local L2 = newlabel()
      self:addJmp("jmp", L2)
      self:fixlabel2here(L1)
      self:codeStat(ast.el)
      self:fixlabel2here(L2)
    end
  elseif tag == "assg" then
    local tyrhs = self:codeExp(ast.exp)
    local tylhs = self:codeLhs(ast.lhs)
    if not typeEq(tyrhs, tylhs) then
      throw("invalid assignment")
    end
  elseif tag == "block" then
    local nvars = #self.locals
    for i = 1, #ast.body do
      self:codeStat(ast.body[i])
    end
    local diff = #self.locals - nvars
    if diff > 0 then
      self:addCode("pop", diff)
      for i = 1, diff do table.remove(self.locals) end
    end
  else error("unknown tag " .. tag)
  end
end


function Compiler:codeFloatExp (ast)
  local ty = self:codeExp(ast)
  if ty.tag ~= "basictype" or ty.ty ~= "float" then
    throw("expression not a number (" .. ast.tag .. ")")
  end
end

local ops = {["+"] = "fadd", ["-"] = "fsub",
             ["*"] = "fmul", ["/"] = "fdiv", 
}

function Compiler:codeExp (ast)
  local tag = ast.tag
  local ty
  if tag == "number" then
    ast.res = string.format("%e", ast.val)
    ty = floatTy
  elseif tag == "var" then
    local loc = self:searchLocal(ast.id)
    if loc then
      ty = loc.ty
      ast.res = self:newreg()
      self:emit("%s = load %s, %s* %s\n",
                ast.res, type2VM(ty), type2VM(ty), loc.idx)
    else
      self:addCode("loadG", self:name2idx(ast.id))
    end
  elseif tag == "indexed" then
    local aty = self:codeExp(ast.array)
    if aty.tag ~= "array" then
      throw("indexing a non array")
    end
    self:codeFloatExp(ast.index)
    self:addCode("getarray")
    ty = aty.elem
  elseif tag == "newarray" then
    self:codeFloatExp(ast.size)
    self:addCode("newarray")
    ty = {tag = "array", elem = ast.ty}
  elseif tag == "not" then
    self:codeFloatExp(ast.e)
    self:addCode("not")
    ty = floatTy
  elseif tag == "neg" then
    self:codeFloatExp(ast.e)
    self:addCode("neg")
    ty = floatTy
  elseif tag == "binop" then
    self:codeFloatExp(ast.e1)
    self:codeFloatExp(ast.e2)
    ty = floatTy
    ast.res = self:newreg()
    self:emit("%s = %s double %s, %s\n",
                  ast.res, ops[ast.op], ast.e1.res, ast.e2.res)
  elseif tag == "conj" then
    local label = newlabel()
    self:codeFloatExp(ast.e1)
    self:addJmp("andjmp", label)
    self:codeFloatExp(ast.e2)
    self:fixlabel2here(label)
    ty = floatTy
  elseif tag == "disj" then
    local label = newlabel()
    self:codeFloatExp(ast.e1)
    self:addJmp("orjmp", label)
    self:codeFloatExp(ast.e2)
    self:fixlabel2here(label)
    ty = floatTy
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
  self:emit("define %s @%s (%s) {\n",
            type2VM(ast.retty), ast.name, params)
  self.funcs[ast.name] = { code = self.code, params = ast.params, retty = ast.retty }
  for i = 1, #self.params do
    local param = self.params[i]
    local addr = count2reg(self:newcount())
    local pty = type2VM(param.ty)
    self:emit("%s = alloca %s\n", addr, pty)
    self:emit("store %s %s, %s* %s\n", pty, param.idx, pty, addr)
    param.idx = addr
  end
  self:codeStat(ast.body)
  self:emit("}\n")
  self:addCode("push", 0)
  self:addCode("ret", #self.params)
end

function compile (ast)
  for i = 1, #ast do
    Compiler:codeFunc(ast[i])
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
