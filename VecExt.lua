-- Extensions to the native Codea vector and matrix types
-- Author: Andrew Stacey
-- Website: http://loopspace.mathforge.com
-- Licence: CC0 http://wiki.creativecommons.org/CC0

--[[
vec4s are promoted to quaternions, vec2s to complex numbers, and other functions are adapted to make use of them
--]]

-- Simplistic error handling

local error = error or print

-- Localise the maths functions/constants that we use for faster lookup.
local abs = math.abs
local pow = math.pow
local sqrt = math.sqrt
local sin = math.sin
local cos = math.cos
local acos = math.acos
local asin = math.asin
local pi = math.pi
local floor = math.floor
local min = math.min
local max = math.max
local exp = math.exp
local log = math.log
local tan = math.tan
local sinh = math.sinh
local cosh = math.cosh
local tanh = math.tanh
local huge = math.huge
local random = math.random

local _modelMatrix = modelMatrix
local _applyMatrix = applyMatrix
local _viewMatrix = viewMatrix
local _projectionMatrix = projectionMatrix
local _rotate = rotate
local _translate = translate
local _scale = scale
local _camera = camera

local _ellipse = ellipse
local _line = line
local _rect = rect
local _sprite = sprite
local _image = image
local _readImage = readImage
local _text = text
local _clip = clip

local tolerance = 0.0000001
local function __quat(a,b,c,d)
    local q = quat()
    q.w = a
    q.x = b
    q.y = c
    q.z = d
    return q
end

local function Heaviside(t)
    local s = floor(t)+.5
    return s/abs(s)/2+.5
end

--[[
The function "is_a" extends the capabilities of the method "is_a" which is automatically defined by Codea for classes.
 
Parameters:
a: object to be tested
b: test
 
The tests work as follows.
 
1. If the type of b is a string, it is taken as the name of a type to test a against.
2. If the type of b is a table, it is assumed to be a class to test if a is an instance thereof.
3. If the type of b is a userdata, the test is to see if a is the same type of object.
4. If b is a function, then it is replaced by the value of that function.
--]]

function is_a(a,b)
    if type(b) == "function" then
        b = b()
    end
    if type(b) == "table" and b.___type then
        b = b()
    end
    if type(b) == "string" then
        return type(a) == b
    end
    if type(b) == "table"
    and type(a) == "table"
    and a.is_a
    then
        return a:is_a(b)
    end
    if type(b) == "userdata"
    and type(a) == "userdata"
    then
        if a.___type or b.___type then
            return a.___type == b.___type
        end
        return  getmetatable(a) == getmetatable(b)
    end
    return false
end

if not edge then
   function edge(t,a,b)
      a,b = a or 0,b or 1
      return min(1,max(0,(t-a)/(b-a)))
   end
end

if not smoothstep then
   function smoothstep(t,a,b)
      a,b = a or 0,b or 1
      t = min(1,max(0,(t-a)/(b-a)))
      return t * t * (3 - 2 * t)
   end
end

if not smootherstep then
   function smootherstep(t,a,b)
      a,b = a or 0,b or 1
      t = min(1,max(0,(t-a)/(b-a)))
      return t * t * t * (t * (t * 6 - 15) + 10)
   end
end

local symbol = readLocalData("Complex Symbol","i")
local rad = readLocalData("Complex Angle","rad")
local angle,angsym
if ra == "rad" then
   angle = 1
   angsym = "π"
else
   angle = 180
   angsym = "°"
end
local precision = readLocalData("Complex Precision",2)
local tostring

function setComplex(t)
   angle = t.angle or angle
   angsym = t.angsym or angsym
   precision = t.precision or precision
   symbol = t.symbol or symbol
   tostring = t.tostring or tostring
end

-- Promote vec2 to complex numbers
m = getmetatable(vec2())

if not m.__extended then
   m["clone"] = function (c)
      return vec2(c.x,c.y)
   end
   
   m["is_finite"] = function (c)
      if c.x < huge
	 and c.x > -huge
	 and c.y < huge
	 and c.y > -huge
      then
	 return true
      end
      return false
   end
   
   m["is_real"] = function (c)
      return c.y == 0
   end
   
   m["is_imaginary"] = function (c)
      return c.x == 0
   end
   
   m["normalise"] = function (c)
      c=c:normalize()
      if c:is_finite() then
	 return c
      else
	 return vec2(1,0)
      end
   end
   
   local add2,sub2 = m["__add"],m["__sub"]
   
   m["__add"] = function (a,b)
      if is_a(a,"number") then
	 a = vec2(a,0)
      end
      if is_a(b,"number") then
	 b = vec2(b,0)
      end
      return add2(a,b)
   end
   
   m["__sub"] = function (a,b)
      if is_a(a,"number") then
	 a = vec2(a,0)
      end
      if is_a(b,"number") then
	 b = vec2(b,0)
      end
      return sub2(a,b)
   end
   
   m["__mul"] = function (a,b)
      if is_a(a,"number") then
	 a = vec2(a,0)
      end
      if is_a(b,"number") then
	 b = vec2(b,0)
      end
      return vec2(a.x*b.x - a.y*b.y,a.x*b.y+a.y*b.x)
   end
   
   m["conjugate"] = function (c)
      return vec2(c.x, - c.y)
   end
   
   m["co"] = m["conjugate"]
   
   function realpower(c,n,k)
      k = k or 0
      local r,t = pow(c:len(),n), (k*2*pi-c:angleBetween(vec2(1,0)))*n
      return vec2(r*cos(t),r*sin(t))
   end
   
   function complexpower(c,w,k)
      if is_a(w,"number") then
	 return realpower(c,w,k)
      end
      if c == vec2(0,0) then
	 error("Taking powers of 0 is somewhat dubious")
	 return false
      end
      local r,t = c:len(),-c:angleBetween(vec2(1,0))
      k = k or 0
      local nr,nt = pow(r,w.x)*exp(-w.y*t),(t+k*2*pi)*w.x+log(r)*w.y
      return vec2(nr*cos(nt),nr*sin(nt))
   end
   
   m["__pow"] = function (c,n)
      if is_a(n,"number") then
	 return realpower(c,n)
      elseif is_a(n,vec2) then
	 return complexpower(c,n)
      else
	 return c:conjugate()
      end
   end
   
   m["__div"] = function (c,q)
      if is_a(q,"number") then
	 return vec2(c.x/q,c.y/q)
      elseif is_a(c,"number") then
	 return c/q:lenSqr()*vec2(q.x,-q.y)
      else
	 return vec2(c.x*q.x+c.y*q.y,c.y*q.x-c.x*q.y)/q:lenSqr()
      end
   end
   
   m["__idiv"] = function (c,q)
	   return vec2(c.x//q,c.y//q)
   end

   m["real"] = function (c)
      return c.x
   end
   
   m["imaginary"] = function (c)
      return c.y
   end
   
   m["__concat"] = function (c,v)
      if is_a(v,vec2) then
	 return c .. v:tostring()
      else
	 return c:tostring() .. v
      end
   end
   
   m["tostring"] = function (c)
      return tostring(c)
   end
   
   function tostringcartesian(c)
      local s
      local x,y = floor(c.x * 10^precision +.5)/10^precision,floor(c.y * 10^precision +.5)/10^precision
      if x ~= 0 then
	 s = x
      end
      if y ~= 0 then
	 if s then
	    if y > 0 then
	       if y == 1 then
		  s = s .. " + " .. symbol
	       else
		  s = s .. " + " .. y .. symbol
	       end
	    else
	       if y == -1 then
		  s = s .. " - " .. symbol
	       else
		  s = s .. " - " .. (-y) .. symbol
	       end
	    end
	 else
	    if y == 1 then
	       s = symbol
	    elseif y == - 1 then
	       s = "-" .. symbol
	    else
	       s = y .. symbol
	    end
	 end
      end
      s = s or "0"
      return s
   end
   
   function tostringpolar (c)
      local t,r = floor(ag *nc:arg() * 10^precision/pi +.5)/10^precision,floor(c:len() * 10^precision +.5)/10^precision
      return "(" .. r .. "," .. t .. angsym .. ")"
   end
   
   tostring = tostringcartesian
   
   m["topolarstring"] = tostringpolar
   m["tocartesianstring"] = tostringcartesian
   
   m["arg"] = function (c)
      return -c:angleBetween(vec2(1,0))
   end
   
   m["tomatrix"] = function(c)
      return matrix(v.x,v.y,0,0,-v.y,v.x,0,0,0,0,1,0,0,0,0,1)
   end
    
    m["len1"] = function(c)
        return abs(c.x) + abs(c.y)
    end
    
    m["dist1"] = function(c,v)
        return abs(c.x - v.x) + abs(c.y - v.y)
    end
    
    m["leninf"] = function(c)
        return max(abs(c.x), abs(c.y))
    end
    
    m["distinf"] = function(c,v)
        return max(abs(c.x - v.x), abs(c.y - v.y))
    end

    m["random"] = function(rnd)
        rnd = rnd or random
        local th = 2*pi*rnd()
        return vec2(cos(th),sin(th))
    end
end

function Complex_unit()
   return vec2(1,0)
end

function Complex_zero()
   return vec2(0,0)
end

function Complex_i()
   return vec2(0,-1)
end

if not math.__extended then
   function math.abs(n)
      if is_a(n,"number") then
	 return abs(n)
      end
      if is_a(n,vec2) then
	 return n:len()
      end
      error("Cannot take the length of " .. n)
   end
   
   function math.pow(n,e)
      if is_a(n,"number") then
	 if is_a(e,"number") then
	    return pow(n,e)
	 elseif is_a(e,vec2) then
	    return realpower(vec2(n,0),e,0)
	 end
      end
      if is_a(n,vec2) then
	 return complexpower(n,e,0)
      end
      error("Cannot take the power of " .. n .. " by " .. e)
   end
   
   function math.sqrt(n)
      if is_a(n,"number") then
	 return sqrt(n)
      end
      if is_a(n,vec2) then
	 return realpower(n,.5,0)
      end
      error("Cannot take the square root of " .. n)
   end
   
   function math.exp(n)
      if is_a(n,"number") then
	 return exp(n)
      end
      if is_a(n,vec2) then
	 local r = exp(n.x)
	 return vec2(r*cos(n.y),r*sin(n.y))
      end
      error("Cannot exponentiate " .. n)
   end
   
   function math.cos(n)
      if is_a(n,"number") then
	 return cos(n)
      end
      if is_a(n,vec2) then
	 return vec2(cos(n.x)*cosh(n.y),-sin(n.x)*sinh(n.y))
      end
      error("Cannot take the cosine of " .. n)
   end
   
   function math.sin(n)
      if is_a(n,"number") then
	 return sin(n)
      end
      if is_a(n,vec2) then
	 return vec2(sin(n.x)*cosh(n.y),cos(n.x)*sinh(n.y))
      end
      error("Cannot take the sine of " .. n)
   end
   
   function math.cosh(n)
      if is_a(n,"number") then
	 return cosh(n)
      end
      if is_a(n,vec2) then
	 return vec2(cosh(n.x)*cos(n.y), sinh(n.x)*sin(n.y))
      end
      error("Cannot take the hyperbolic cosine of " .. n)
   end
   
   function math.sinh(n)
      if is_a(n,"number") then
	 return sinh(n)
      end
      if is_a(n,vec2) then
	 return vec2(sinh(x)*cos(y), cosh(x)*sin(y))
      end
      error("Cannot take the hyperbolic sine of " .. n)
   end
   
   function math.tan(n)
      if is_a(n,"number") then
	 return tan(n)
      end
      if is_a(n,vec2) then
	 local cx,sx,chy,shy = cos(n.x),sin(n.x),cosh(n.y),sinh(n.y)
	 local d = cx^2 * chy^2 + sx^2 * shy^2
	 if d == 0 then
	    return false
	 end
	 return vec2(sx*cx/d,shy*chy/d)
      end
      error("Cannot take the tangent of " .. n)
   end
   
   function math.tanh(n)
      if is_a(n,"number") then
	 return tanh(n)
      end
      if is_a(n,vec2) then
	 local cx,sx,chy,shy = cos(n.x),sin(n.x),cosh(n.y),sinh(n.y)
	 local d = cx^2 * chy^2 + sx^2 * shy^2
	 if d == 0 then
	    return false
	 end
	 return vec2(shx*chx/d,sy*cy/d)
      end
      error("Cannot take the hyperbolic tangent of " .. n)
   end
   
   function math.log(n,k)
      if is_a(n,"number") then
	 if k then
	    return vec2(log(n), 2*k*pi)
	 else
	    return log(n)
	 end
      end
      k = k or 0
      if is_a(n,vec2) then
	 return vec2(log(n:len()),n:arg() + 2*k*pi)
      end
      error("Cannot take the logarithm of " .. n)
   end
    
    math.olog = log
   
   m.__extended = true
end

m = getmetatable(vec4())
if not m.__extended then
   m["is_finite"] = function(q)
      if q.x < huge
	 and q.x > -huge
	 and q.y < huge
	 and q.y > -huge
	 and q.z < huge
	 and q.z > -huge
	 and q.w < huge
	 and q.w > -huge
      then
	 return true
      end
      return false
   end
   
   m["is_real"] = function (q)
      if q.y ~= 0
	 or q.z ~= 0
	 or q.w ~= 0
      then
	 return false
      end
      return true
   end
   
   m["is_imaginary"] = function (q)
      return q.x == 0
   end
   
   m["normalise"] = function (q)
      q = q:normalize()
      if q:is_finite() then
	 return q
      else
	 return vec4(1,0,0,0)
      end
   end
   
   m["slen"] = function(q) 
      q = q:normalise()
      q.x = q.x - 1
      return 2*asin(q:len()/2)
   end
   
   m["sdist"] = function(q,qq)
      q = q:normalise()
      qq = qq:normalise()
      return 2*asin(q:dist(qq)/2)
   end
    
    m["len1"] = function(c)
        return abs(c.x) + abs(c.y) + abs(c.z) + abs(c.w)
    end
    
    m["dist1"] = function(c,v)
        return abs(c.x - v.x) + abs(c.y - v.y) + abs(c.z - v.z) + abs(c.w - v.w)
    end
    
    m["leninf"] = function(c)
        return max(abs(c.x), abs(c.y), abs(c.z), abs(c.w))
    end
    
    m["distinf"] = function(c,v)
        return max(abs(c.x - v.x), abs(c.y - v.y), abs(c.z - v.z), abs(c.w - v.w))
    end
   
   local add4,sub4,mul4,div4 = m["__add"],m["__sub"],m["__mul"],m["__div"]
   
   m["__add"] = function (a,b)
      if is_a(a,"number") then
	 a = vec4(a,0,0,0)
      end
      if is_a(b,"number") then
	 b = vec4(b,0,0,0)
      end
      return add4(a,b)
   end
   
   m["__sub"] = function (a,b)
      if is_a(a,"number") then
	 a = vec4(a,0,0,0)
      end
      if is_a(b,"number") then
	 b = vec4(b,0,0,0)
      end
      return sub4(a,b)
   end
   
   m["__mul"] = function (a,b)
      if is_a(a,"number") then
	 return mul4(a,b)
      end
      if is_a(b,"number") then
	 return mul4(a,b)
      end
      if is_a(a,matrix) then
	 return a:__mul(b:tomatrixleft())
      end
      if is_a(b,matrix) then
	 return a:tomatrixleft():__mul(b)
      end
      return vec4(
	 a.x * b.x - a.y * b.y - a.z * b.z - a.w * b.w,
	 a.x * b.y + a.y * b.x + a.z * b.w - a.w * b.z,
	 a.x * b.z - a.y * b.w + a.z * b.x + a.w * b.y,
	 a.x * b.w + a.y * b.z - a.z * b.y + a.w * b.x
		 )
   end
   
   m["conjugate"] = function (q)
      return vec4(q.x, - q.y, - q.z, - q.w)
   end
   
   m["co"] = m["conjugate"]
   
   m["__div"] = function (a,b)
      if is_a(b,"number") then
	 return div4(a,b)
      end
      local l = b:lenSqr()
      b = vec4(b.x/l,-b.y/l,-b.z/l,-b.w/l)
      if is_a(a,"number") then
	 return vec4(a*b.x,a*b.y,a*b.z,a*b.w)
      end
      return vec4(
	 a.x * b.x - a.y * b.y - a.z * b.z - a.w * b.w,
	 a.x * b.y + a.y * b.x + a.z * b.w - a.w * b.z,
	 a.x * b.z - a.y * b.w + a.z * b.x + a.w * b.y,
	 a.x * b.w + a.y * b.z - a.z * b.y + a.w * b.x
		 )
   end
   
   m["__idiv"] = function (q,l)
	   return vec4(q.x//l,q.y//l,q.z//l,q.w//l)
   end
    
   function integerpower(q,n)
      if n == 0 then
	 return vec4(1,0,0,0)
      elseif n > 0 then
	 return q:__mul(integerpower(q,n-1))
      elseif n < 0 then
	 local l = q:lenSqr()
	 q = vec4(q.x/l,-q.y/l,-q.z/l,-q.w/l)
	 return integerpower(q,-n)
      end
   end
   
   function realpower(q,n)
      if n == floor(n) then
	 return integerpower(q,n)
      end
      local l = q:len()
      q = q:normalise()
      return l^n * q:slerp(n)
   end
   
   m["__pow"] = function (q,n)
      if is_a(n,"number") then
	 return realpower(q,n)
      elseif is_a(n,vec4) then
	 return n:__mul(q):__div(n)
      else
	 return q:conjugate()
      end
   end
   
   m["lerp"] = function (q,qq,t)
      if not t then
	 q,qq,t = vec4(1,0,0,0),q,qq
      end
      if (q + qq):len() == 0 then
	 q = (1 - 2*t) * q + (1 - abs(2*t - 1)) * vec4(q.y,-q.x,q.w,-q.z)
      else
	 q = (1-t)*q + t*qq
      end
      return q:normalise()
   end
   
   m["slerp"] = function (q,qq,t)
      if not t then
	 q,qq,t = vec4(1,0,0,0),q,qq
      end
      if (q + qq):len() == 0 then
	 qq,t = vec4(q.y,-q.x,q.w,-q.z),2*t
      elseif (q - qq):len() == 0 then
	 return q
      end
      local ca = q:dot(qq)
      local sa = sqrt(1 - pow(ca,2))
      if sa == 0 or sa ~= sa then
	 return q
      end
      local a = acos(ca)
      sa = sin(a*t)/sa
      return (cos(a*t)-ca*sa)*q+sa*qq
   end
   
   m["make_lerp"] = function (q,qq)
      if not qq then
	 q,qq = vec4(1,0,0,0),q
      end
      q,qq = q:normalise(),qq:normalise()
      if (q + qq):len() == 0 then
	 qq = vec4(q.y,-q.x,q.w,-q.z)
	 return function(t)
	    return ((1-2*t)*q+(1-abs(2*t-1))*qq):normalise()
		end
      else
	 return function(t)
	    return ((1-t)*q+t*qq):normalise()
		end
	 
      end
   end
   
   m["make_slerp"] = function (q,qq)
      if not qq then
	 q,qq = vec4(1,0,0,0),q
      end
      q,qq = q:normalise(),qq:normalise()
      local f
      if (q + qq):len() == 0 then
	 qq,f = vec4(q.y,-q.x,q.w,-q.z),2
      elseif (q - qq):len() == 0 then
	 return function(t)
	    return q
		end
      else
	 f = 1
      end
      local ca = q:dot(qq)
      local sa = sqrt(1 - pow(ca,2))
      if sa == 0 or sa ~= sa then
	 return function(t)
	    return q
		end
      end
      local a = acos(ca)
      qq = (qq - ca*q)/sa
      return function(t)
	 return cos(a*f*t)*q + sin(a*f*t)*qq
	     end
   end
   
   m["toreal"] = function (q)
      return q.x
   end
   
   m["vector"] = function (q)
      return vec3(q.y, q.z, q.w)
   end
   
   m["tovector"] = m["vector"]
   
   m["log"] = function (q)
      local l = q:slen()
      q = q:tovector():normalize()
      if not q:is_finite() then
	 return vec3(0,0,0)
      else
	 return q * l
      end
   end
   
   m["tostring"] = function (q)
      local s
      local im = {{q.y,"i"},{q.z,"j"},{q.w,"k"}}
      if q.x ~= 0 then
	 s = string.format("%.3f",q.x)
      end
      for k,v in pairs(im) do
	 if v[1] ~= 0 then
	    if s then
	       if v[1] > 0 then
		  if v[1] == 1 then
		     s = s.." + "..v[2]
		  else
		     s = s.." + "..string.format("%.3f",v[1])..v[2]
		     
		  end
	       else
		  if v[1] == -1 then
		     s = s.." - "..v[2]
		  else
		     s = s.." - "..string.format("%.3f",-v[1])..v[2]
		  end
	       end
	    else
	       if v[1] == 1 then
		  s = v[2]
	       elseif v[1] == - 1 then
		  s = "-" .. v[2]
	       else
		  s = string.format("%.3f",v[1]) .. v[2]
	       end
	    end
	 end
      end
      s = s or "0"
      return s
   end
   
   m["__concat"] = function (q,s)
      if is_a(s,"string") then
	 return q:tostring() .. s
      else
	 return q .. s:tostring()
      end
   end
   
   m["tomatrixleft"] = function (q)
      q = q:normalise()
      local a,b,c,d = q.x,q.y,q.z,q.w
      local ab,ac,ad,bb,bc,bd,cc,cd,dd = 2*a*b,2*a*c,2*a*d,2*b*b,2*b*c,2*b*d,2*c*c,2*c*d,2*d*d
      return matrix(
	 1-cc-dd, bc-ad, ac+bd, 0,
	 bc+ad, 1-bb-dd, cd-ab, 0,
	 bd-ac, cd+ab, 1-bb-cc, 0,
	 0,0,0,1
		   )
   end
   
   m["tomatrixright"] = function (q)
      q = q:normalise()
      local a,b,c,d = q.x,-q.y,-q.z,-q.w
      local ab,ac,ad,bb,bc,bd,cc,cd,dd = 2*a*b,2*a*c,2*a*d,2*b*b,2*b*c,2*b*d,2*c*c,2*c*d,2*d*d
      return matrix(
	 1-cc-dd, bc-ad, ac+bd, 0,
	 bc+ad, 1-bb-dd, cd-ab, 0,
	 bd-ac, cd+ab, 1-bb-cc, 0,
	 0,0,0,1
		   )
   end
   
   m["tomatrix"] = m["tomatrixright"]
   
   m["toangleaxis"] = function (q)
      q = q:normalise()
      local a = q.x
      q = vec3(q.y,q.z,q.w)
      if q == vec3(0,0,0) then
	 return 0,vec3(0,0,1)
      end
      return 2*acos(a),q:normalise()
   end
   
   m["Gravity"] = function (q)
      local y = vec3(0,-1,0)^q
      return y:rotateTo(Gravity)*q
   end
   m.__extended = true
end

if not qGravity then
   function qGravity()
      if Gravity.x == 0
	 and Gravity.y == 0
      then
	 return vec4(1,0,0,0)
      else
	 local gxy, gy, gygxy, a, b, c, d
	 gy,gxy = - Gravity.y,sqrt(pow(Gravity.x,2) + pow(Gravity.y,2))
	 gygxy = gy/gxy
	 a,b,c,d = sqrt(1 + gxy - gygxy - gy)/2, sqrt(1 - gxy - gygxy + gy)/2, sqrt(1 - gxy + gygxy - gy)/2, sqrt(1 + gxy + gygxy + gy)/2
	 if Gravity.z < 0 then
	    b,c = - b,-c
	 end
	 if Gravity.x > 0 then
	    c,d = - c,-d
	 end
	 return vec4(a,b,c,d)
      end
   end
    
   function quatGravity()
      if Gravity.x == 0
	 and Gravity.y == 0
      then
	 return __quat(1,0,0,0)
      else
	 local gxy, gy, gygxy, a, b, c, d
	 gy,gxy = - Gravity.y,sqrt(pow(Gravity.x,2) + pow(Gravity.y,2))
	 gygxy = gy/gxy
	 a,b,c,d = sqrt(1 + gxy - gygxy - gy)/2, sqrt(1 - gxy - gygxy + gy)/2, sqrt(1 - gxy + gygxy - gy)/2, sqrt(1 + gxy + gygxy + gy)/2
	 if Gravity.z < 0 then
	    b,c = - b,-c
	 end
	 if Gravity.x > 0 then
	    c,d = - c,-d
	 end
	 return __quat(a,b,c,d)
      end
   end
   
   function qRotation(a,x,y,z)
        local q,c,s
        if not y then
            x,y,z = x.x,x.y,x.z
        end
        q = vec4(0,x,y,z):normalise()
        if q == vec4(1,0,0,0) then
            return q
        end
        return q:__mul(sin(a/2)):__add(cos(a/2))
   end
   
   local euler = {}
   euler.x = function(q)
      return vec3(1,0,0)^q
   end
   euler.X = function(q)
      return vec3(1,0,0)
   end
   euler.y = function(q)
      return vec3(0,1,0)^q
   end
   euler.Y = function(q)
      return vec3(0,1,0)
   end
   euler.z = function(q)
      return vec3(0,0,1)^q
   end
   euler.Z = function(q)
      return vec3(0,0,1)
   end
   
   function qEuler(a,b,c,v)
      if c then
	 a = {a,b,c}
      else
	 if is_a(a,vec3) then
	    a = {a.x,a.y,a.z}
	 end v = b
      end
      v = v or {"x","y","z"}
      local q = vec4(1,0,0,0)
      for k,u in ipairs(v) do
	 q = q * qRotation(a[k],euler[u](q))
      end
      return q
   end
   
   function qTangent(x,y,z,t)
      local q
      if is_a(x,"number") then
	 q,t = vec4(0,x,y,z), t or 1
      else
	 q,t = vec4(0,x.x,x.y,x.z), y or 1
      end
      local qn = q:normalise()
      if qn == vec4(1,0,0,0) then
	 return qn
      end
      t = t * q:len()
      return cos(t)*vec4(1,0,0,0) + sin(t)*qn
   end
   
   function qRotationRate()
      return qTangent(DeltaTime * RotationRate)
   end
   
    function quatRotationRate()
      return quat.tangent(DeltaTime * RotationRate)
   end

   function modelMatrix(m)
      if m then
	 if is_a(m,vec4) then
	    m = m:tomatrixright()
	 elseif is_a(m,quat) then
	    m = m:tomatrixright()
	 elseif is_a(m,vec2) then
	    m = m:tomatrix()
	 end
	 return _modelMatrix(m)
      else
	 return _modelMatrix()
      end
   end
   
   function applyMatrix(m)
      if m then
	 if is_a(m,vec4) then
	    m = m:tomatrixright()
	 elseif is_a(m,quat) then
	    m = m:tomatrixright()
	 elseif is_a(m,vec2) then
	    m = m:tomatrix()
	 end
	 return _applyMatrix(m)
      else
	 return _applyMatrix()
      end
   end
   
   function viewMatrix(m)
      if m then
	 if is_a(m,vec4) then
	    m = m:tomatrixright()
	 elseif is_a(m,quat) then
	    m = m:tomatrixright()
	 elseif is_a(m,vec2) then
	    m = m:tomatrix()
	 end
	 return _viewMatrix(m)
      else
	 return _viewMatrix()
      end
   end
   
   function projectionMatrix(m)
      if m then
	 if is_a(m,vec4) then
	    m = m:tomatrixright()
	 elseif is_a(m,quat) then
	    m = m:tomatrixright()
	 elseif is_a(m,vec2) then
	    m = m:tomatrix()
	 end
	 return _projectionMatrix(m)
      else
	 return  _projectionMatrix()
      end
   end
    
    function resetMatrices()
        resetMatrix()
        viewMatrix(matrix())
        ortho()
    end
   
   function rotate(a,x,y,z)
      if is_a(a,vec4) then
	 local v
	 a,v = a:toangleaxis()
	 x,y,z,a = v.x,v.y,v.z,a*180/pi
      end
      if is_a(a,quat) then
	 local v
	 a,v = a:toangleaxis()
	 x,y,z,a = v.x,v.y,v.z,a*180/pi
      end
      if x then
	 return _rotate(a,x,y,z)
      end
      return _rotate(a)
   end
   
   function translate(x,y,z)
      if not y then
	 x,y,z = x.x,x.y,x.z
      end
      if z then
	 return _translate(x,y,z)
      end
      return _translate(x,y)
   end
   
   function scale(a,b,c)
      if is_a(a,vec3) then
	 a,b,c = a.x,a.y,a.z
      end
      if is_a(a,vec2) then
	 a,b,c = a.x,a.y,b
      end
      if c then
	 return _scale(a,b,c)
      end
      if b then
	 return _scale(a,b)
      end
      if a then
	 return _scale(a)
      end
      return _scale()
   end
   
   function camera(a,b,c,d,e,f,g,h,i)
      if is_a(a,vec3) then
	 a,b,c,d,e,f,g,h,i = a.x,a.y,a.z,b,c,d,e,f,g
        end
      if is_a(d,vec3) then
	 d,e,f,g,h,i = d.x,d.y,d.z,e,f,g
      end
      if is_a(g,vec3) then
	 g,h,i = g.x,g.y,g.z
      end
      if g then
	 return _camera(a,b,c,d,e,f,g,h,i)
      elseif d then
	 return _camera(a,b,c,d,e,f)
      elseif a then
	 return _camera(a,b,c)
      else
	 return _camera()
      end
   end
   
   function line(a,b,c,d)
      if is_a(a,vec2) then
	 a,b,c,d = a.x,a.y,b,c
      end
      if is_a(c,vec2) then
	 c,d = c.x,c.y
      end
      _line(a,b,c,d)
   end
   
   function ellipse(a,b,c,d)
      if is_a(a,vec2) then
	 a,b,c,d = a.x,a.y,b,c
      end
      if is_a(c,vec2) then
	 c,d = c.x,c.y
      end
      if d then
	 _ellipse(a,b,c,d)
      else
	 _ellipse(a,b,c)
      end
   end
   
   function rect(a,b,c,d)
      if is_a(a,vec2) then
	 a,b,c,d = a.x,a.y,b,c
      end
      if is_a(c,vec2) then
	 c,d = c.x,c.y
      end
      if d then
	 _rect(a,b,c,d)
      else
	 _rect(a,b,c)
      end
   end
    
   function clip(a,b,c,d)
      if is_a(a,vec2) then
	 a,b,c,d = a.x,a.y,b,c
      end
      if is_a(c,vec2) then
	 c,d = c.x,c.y
      end
      if a then
	 _clip(a,b,c,d)
      else
	 _clip()
      end
   end
   
   function sprite(a,x,y,w,h)
      if is_a(x,vec2) then
	 x,y,w,h = x.x,x.y,y,w
      end
      if h then
	 _sprite(a,x,y,w,h)
      elseif w then
	 _sprite(a,x,y,w)
      elseif x then
	 _sprite(a,x,y)
            else
            _sprite(a)
      end
   end
    
   function readImage(a,w,h,n)
      if is_a(w,vec2) then
            w,h,n = w.x,w.y,h
      end
      if n then
	 return _readImage(a,w,h,n)
      elseif h then
	return _readImage(a,w,h)
      elseif w then
	 return _readImage(a,w)
            else
           return _readImage(a)
      end
   end
    
    function image(w,h)
        if is_a(w,vec2) then
            w,h = w.x,w.y
        end
        if h then
            return _image(w,h)
        end
        return _image(w)
    end
   
   function text(a,x,y)
      if is_a(x,vec2) then
	 x,y = x.x,x.y
      end
        if x then
      _text(a,x,y)
        else
            _text(a)
        end
   end
end

m = getmetatable(vec3())
if not m.__extended then
   m["is_finite"] = function(v)
      if v.x < huge
	 and v.x > -huge
	 and v.y < huge
	 and v.y > -huge
	 and v.z < huge
	 and v.z > -huge
      then
	 return true
      end
      return false
   end
   
   m["toQuaternion"] = function (v)
      return vec4(0,v.x,v.y,v.z)
   end
   
   m["applyQuaternion"] = function (v,q)
      return q:__mul(v:toQuaternion()):__mul(q:conjugate()):vector()
   end

    m["toquat"] = function (v)
        return __quat(0,v.x,v.y,v.z)
    end
    
    m["applyquat"] = function (v,q)
        return q:__mul(v:toquat()):__mul(q:conjugate()):vector()
    end
    
    m["rotate"] = function(v,q,x,y,z)
        if is_a(q,"number") then
            if is_a(x,"number") then
                x = vec3(x,y,z)
            end
            q = quat.angleAxis(q,x)
        end
        return v:applyquat(q)
    end
    
   m["__pow"] = function (v,q)
        if is_a(q,quat) then
            return v:applyquat(q)
        end
        if is_a(q,vec4) then
            return v:applyQuaternion(q)
        end
        return false
    end
   
   m["__concat"] = function (u,s)
      if is_a(s,"string") then
	 return u:__tostring() .. s
      else
	 return u .. s:__tostring()
      end
   end
   
    m["rotateTo"] = function (u,v)
        if v:cross(u):len() < tolerance then
            if v:dot(u) >= -tolerance then
                return vec4(1,0,0,0)
            end
            u = u:normalize()
            local a,b,c = abs(u.x), abs(u.y), abs(u.z)
            if a < b
            and a < c then
                v = vec3(0,-u.z,u.y)
            elseif b < c then
                v = vec3(u.z,0,-u.x)
            else
                v = vec3(u.y,-u.x,0)
            end
        else
            u = u:normalise()
            v = u + v:normalise()
        end
        v = v:normalise()
        local d = u:dot(v)
        u = u:cross(v)
        return vec4(d,u.x,u.y,u.z)
    end
    
    m["rotateToquat"] = function (u,v)
        local q = quat.fromToRotation(u,v)
        if q == quat(1,0,0,0) and -u:dot(v) > u:len()*v:len() - tolerance then
            local qv = u:rotateTo(v)
            q = __quat(qv.x,qv.y,qv.z,qv.w)
        end
        return q
    end
   
   m["normalise"] = function (v)
      v = v:normalize()
      if v:is_finite() then
	 return v
      else
	 return vec3(0,0,1)
      end
   end
   
   local mul3,add3,sub3 = m["__mul"],m["__add"],m["__sub"]
   m["__mul"] = function(m,v)
      if is_a(m,vec3)
	 and is_a(v,"number")
      then
	 return mul3(m,v)
      end
      if is_a(m,"number")
	 and is_a(v,vec3)
      then
	 return mul3(m,v)
      end
      if is_a(m,vec3)
	 and is_a(v,vec3)
      then
	 return vec3(m.x*v.x,m.y*v.y,m.z*v.z)
      end
      if is_a(m,matrix)
	 and is_a(v,vec3)
      then
	 local l = m[13]*v.x+m[14]*v.y+m[15]*v.z+m[16]
	 return vec3(
	    (m[1]*v.x + m[2]*v.y + m[3]*v.z + m[4])/l,
	    (m[5]*v.x + m[6]*v.y + m[7]*v.z + m[8])/l,
	    (m[9]*v.x + m[10]*v.y + m[11]*v.z + m[12])/l)
      end
      if is_a(m,vec3)
	 and is_a(v,matrix)
      then
	 local l = v[4]*m.x+v[8]*m.y+v[12]*m.z+v[16]
	 return vec3(
	    (v[1]*m.x + v[5]*m.y + v[9]*m.z + v[13])/l,
	    (v[2]*m.x + v[6]*m.y + v[10]*m.z + v[14])/l,
	    (v[3]*m.x + v[7]*m.y + v[11]*m.z + v[15])/l)
      end
   end
   
   m["__add"] = function(a,b)
      if is_a(a,"number") then
	 a = vec3(a,a,a)
      end
      if is_a(b,"number") then
	 b = vec3(b,b,b)
      end
      return add3(a,b)
   end
   
   m["__sub"] = function(a,b)
      if is_a(a,"number") then
	 a = vec3(a,a,a)
      end
      if is_a(b,"number") then
	 b = vec3(b,b,b)
      end
      return sub3(a,b)
   end
    
   m["__idiv"] = function (q,l)
	   return vec3(q.x//l,q.y//l,q.z//l)
   end
   
   m["exp"] = qTangent
    
    m["len1"] = function(c)
        return abs(c.x) + abs(c.y) + abs(c.z)
    end
    
    m["dist1"] = function(c,v)
        return abs(c.x - v.x) + abs(c.y - v.y) + abs(c.z - v.z)
    end
    
    m["leninf"] = function(c)
        return max(abs(c.x), abs(c.y), abs(c.z))
    end
    
    m["distinf"] = function(c,v)
        return max(abs(c.x - v.x), abs(c.y - v.y), abs(c.z - v.z))
    end
   
    m["random"] = function(rnd)
        rnd = rnd or random
        local th = 2*pi*rnd()
        local z = 2*rnd() - 1
        local r = sqrt(1 - z*z)
        return vec3(r*cos(th),r*sin(th),z)
    end
    
    m["orthogonal"] = function(v)
        local x,y,z = abs(v.x), abs(v.y), abs(v.z)
        local xy = Heaviside(x-y)
        local yz = Heaviside(y-z)
        local zx = Heaviside(z-x)
        return v:cross(vec3(
            zx*(1-xy) + xy*yz*zx,
            xy*(1-yz),
            yz*(1-zx)
        ))
    end
    
   m.__extended = true
end

m = getmetatable(matrix())
if not m.__extended then
   local mmul, mrotate = m["__mul"],m["rotate"]
   
   m["__mul"] = function (m,mm)
      if is_a(m,matrix)
	 and is_a(mm,matrix)
      then
	 return mmul(m,mm)
      end
        if is_a(m,matrix)
        and is_a(mm,quat)
        then
            return mmul(m,qQuat(mm):tomatrix())
        end
        if is_a(m,quat)
        and is_a(mm,matrix)
        then
            return mmul(qQuat(m):tomatrix(),mm)
        end
      if is_a(m,matrix)
	 and is_a(mm,vec4)
      then
	 return mmul(m,mm:tomatrix())
      end
      if is_a(m,vec4)
	 and is_a(mm,matrix)
      then
	 return mmul(m:tomatrix(),mm)
      end
      if is_a(m,matrix)
	 and is_a(mm,vec2)
      then
	 return mmul(m,mm:tomatrix())
      end
      if is_a(m,vec2)
	 and is_a(mm,matrix)
      then
	 return mmul(m:tomatrix(),mm)
      end
      if is_a(m,matrix)
	 and is_a(mm,vec3)
      then
	 local l = m[13]*mm.x + m[14]*mm.y + m[15]*mm.z + m[16]
	 return vec3(
	    (m[1]*mm.x + m[2]*mm.y + m[3]*mm.z + m[4])/l,
	    (m[5]*mm.x + m[6]*mm.y + m[7]*mm.z + m[8])/l,
	    (m[9]*mm.x + m[10]*mm.y + m[11]*mm.z + m[12])/l)
      end
      if is_a(m,vec3)
	 and is_a(mm,matrix)
      then
	 local l = mm[4]*m.x + mm[8]*m.y + mm[12]*m.z + mm[16]
	 return vec3(
	    (mm[1]*m.x + mm[5]*m.y + mm[9]*m.z + mm[13])/l,
	    (mm[2]*m.x + mm[6]*m.y + mm[10]*m.z + mm[14])/l,
	    (mm[3]*m.x + mm[7]*m.y + mm[11]*m.z + mm[15])/l)
      end
   end
   
   m["rotate"] = function(m,a,x,y,z)
      if is_a(a,vec4) then
	 a,x = a:toangleaxis()
	 x,y,z = x.x,x.y,x.z
      end
        if is_a(a,quat) then
            a,x = a:toangleaxis()
            x,y,z = x.x,x.y,x.z
        end
      return mrotate(m,a,x,y,z)
   end
   
   m.__extended = true
end

function extendQuat()
    local mq,m
    mq = getmetatable(quat())
    if mq.__extended then
        return
    end
    
    m = {}
    m["is_finite"] = function(q)
        if q.x < huge
        and q.x > -huge
        and q.y < huge
        and q.y > -huge
        and q.z < huge
        and q.z > -huge
        and q.w < huge
        and q.w > -huge
        then
            return true
        end
        return false
    end
    
    m["is_real"] = function (q)
        if q.y ~= 0
        or q.z ~= 0
        or q.x ~= 0
        then
            return false
        end
        return true
    end
    
    m["is_imaginary"] = function (q)
        return q.w == 0
    end
    
    m["normalise"] = function (q)
        q = q:normalize()
        if q:is_finite() then
            return q
        else
            return __quat(1,0,0,0)
        end
    end
    
    m["len"] = function(q)
        return sqrt(q.x*q.x+q.y*q.y+q.z*q.z+q.w*q.w)
    end
    
    m["lenSqr"] = function(q)
        return q.x*q.x+q.y*q.y+q.z*q.z+q.w*q.w
    end
    
    m["dist"] = function(q,qq)
        return sqrt((q.x-qq.x)^2+(q.y-qq.y)^2+(q.z-qq.z)^2+(q.w-qq.w)^2)
    end
    
    m["distSqr"] = function(q,qq)
        return (q.x-qq.x)^2+(q.y-qq.y)^2+(q.z-qq.z)^2+(q.w-qq.w)^2
    end
    
    m["dot"] = function(q,qq)
        return q.x*qq.x + q.y*qq.y + q.z*qq.z + q.w*qq.w
    end
    
    m["normalize"] = function(q)
        return q/q:len()
    end
    
    m["slen"] = function(q)
        q = q:normalise()
        q.w = q.w - 1
        return 2*asin(q:len()/2)
    end
    
    m["sdist"] = function(q,qq)
        q = q:normalise()
        qq = qq:normalise()
        return 2*asin(q:dist(qq)/2)
    end
    
    m["len1"] = function(c)
        return abs(c.x) + abs(c.y) + abs(c.z) + abs(c.w)
    end
    
    m["dist1"] = function(c,v)
        return abs(c.x - v.x) + abs(c.y - v.y) + abs(c.z - v.z) + abs(c.w - v.w)
    end
    
    m["leninf"] = function(c)
        return max(abs(c.x), abs(c.y), abs(c.z), abs(c.w))
    end
    
    m["distinf"] = function(c,v)
        return max(abs(c.x - v.x), abs(c.y - v.y), abs(c.z - v.z), abs(c.w - v.w))
    end
    
    local mulq = mq["__mul"]
    
    rawset(quat,"tangent",function(x,y,z,t)
        local q
        if is_a(x,"number") then
            q,t = __quat(0,x,y,z), t or 1
        else
            q,t = __quat(0,x.x,x.y,x.z), y or 1
        end
        local qn = q:normalise()
        if qn == __quat(1,0,0,0) then
            return qn
        end
        t = t * q:len()
        return cos(t)*__quat(1,0,0,0) + sin(t)*qn
    end)
    
    rawset(quat,"random",function(rnd)
        rnd = rnd or random
        local u,v,w = rnd(),2*pi*rnd(),2*pi*rnd()
        local s,t = sqrt(1-u),sqrt(u)
        return __quat(s*sin(v),s*cos(v),t*sin(w),t*cos(w))
    end)
    
    m["__add"] = function (a,b)
        if is_a(a,"number") then
            a = __quat(a,0,0,0)
        end
        if is_a(b,"number") then
            b = __quat(b,0,0,0)
        end
        return __quat(a.w+b.w,a.x+b.x,a.y+b.y,a.z+b.z)
    end
    
    m["__sub"] = function (a,b)
        if is_a(a,"number") then
            a = __quat(a,0,0,0)
        end
        if is_a(b,"number") then
            b = __quat(b,0,0,0)
        end
        return __quat(a.w-b.w,a.x-b.x,a.y-b.y,a.z-b.z)
    end
    
    m["__mul"] = function (a,b)
        if is_a(a,"number") then
            return __quat(a*b.w,a*b.x,a*b.y,a*b.z)
        end
        if is_a(b,"number") then
            return __quat(a.w*b,a.x*b,a.y*b,a.z*b)
        end
        if is_a(a,matrix) then
            return a:__mul(b:tomatrixleft())
        end
        if is_a(b,matrix) then
            return a:tomatrixleft():__mul(b)
        end
        return mulq(a,b)
    end
    
    m["conjugate"] = function (q)
        return __quat(q.w,-q.x,-q.y,-q.z)
    end
    
    m["co"] = m["conjugate"]
    
    m["__div"] = function (a,b)
        if is_a(b,"number") then
            return __quat(a.w/b,a.x/b,a.y/b,a.z/b)
        end
        local l = b:lenSqr()
        b = __quat(b.w/l,-b.x/l,-b.y/l,-b.z/l)
        if is_a(a,"number") then
            return __quat(a*b.w,a*b.x,a*b.y,a*b.z)
        end
        return mulq(a,b)
    end
    
    function integerpower(q,n)
        if n == 0 then
            return __quat(1,0,0,0)
        elseif n > 0 then
            return q:__mul(integerpower(q,n-1))
        elseif n < 0 then
            local l = q:lenSqr()
            q = __quat(q.w/l,-q.x/l,-q.y/l,-q.z/l)
            return integerpower(q,-n)
        end
    end
    
    function realpower(q,n)
        if n == floor(n) then
            return integerpower(q,n)
        end
        local l = q:len()
        q = q:normalise()
        return l^n * q:slerp(n)
    end
    
    m["__pow"] = function (q,n)
        if is_a(n,"number") then
            return realpower(q,n)
        elseif is_a(n,quat) then
            return n:__mul(q):__div(n)
        else
            return q:conjugate()
        end
    end
    
    m["lerp"] = function (q,qq,t)
        if not t then
            q,qq,t = __quat(1,0,0,0),q,qq
        end
        if (q + qq):len() == 0 then
            q = (1 - 2*t) * q + (1 - abs(2*t - 1)) * __quat(q.x,-q.w,q.z,-q.y)
        else
            q = (1-t)*q + t*qq
        end
        return q:normalise()
    end
    --[[
    m["slerp"] = function (q,qq,t)
        if not t then
            q,qq,t = quat(1,0,0,0),q,qq
        end
        if (q + qq):len() == 0 then
            qq,t = quat(q.x,-q.w,q.z,-q.y),2*t
        elseif (q - qq):len() == 0 then
            return q
        end
        local ca = q:dot(qq)
        local sa = sqrt(1 - pow(ca,2))
        if sa == 0 or sa ~= sa then
            return q
        end
        local a = acos(ca)
        sa = sin(a*t)/sa
        return (cos(a*t)-ca*sa)*q+sa*qq
    end
    --]]
    m["make_lerp"] = function (q,qq)
        if not qq then
            q,qq = __quat(1,0,0,0),q
        end
        q,qq = q:normalise(),qq:normalise()
        if (q + qq):len() == 0 then
            qq = __quat(q.x,-q.w,q.z,-q.y)
            return function(t)
                return ((1-2*t)*q+(1-abs(2*t-1))*qq):normalise()
            end
        else
            return function(t)
                return ((1-t)*q+t*qq):normalise()
            end
            
        end
    end
    
    m["make_slerp"] = function (q,qq)
        if not qq then
            q,qq = __quat(1,0,0,0),q
        end
        q,qq = q:normalise(),qq:normalise()
        local f
        if (q + qq):len() == 0 then
            qq,f = __quat(q.x,-q.w,q.z,-q.y),2
        elseif (q - qq):len() == 0 then
            return function(t)
                return q
            end
        else
            f = 1
        end
        local ca = q:dot(qq)
        local sa = sqrt(1 - pow(ca,2))
        if sa == 0 or sa ~= sa then
            return function(t)
                return q
            end
        end
        local a = acos(ca)
        qq = (qq - ca*q)/sa
        return function(t)
            return cos(a*f*t)*q + sin(a*f*t)*qq
        end
    end
    
    m["toreal"] = function (q)
        return q.w
    end
    
    m["vector"] = function (q)
        return vec3(q.x, q.y, q.z)
    end
    
    m["tovector"] = m["vector"]
    
    m["log"] = function (q)
        local l = q:slen()
        q = q:tovector():normalize()
        if not q:is_finite() then
            return vec3(0,0,0)
        else
            return q * l
        end
    end
    
    m["tostring"] = function (q)
        local s
        local im = {{q.x,"i"},{q.y,"j"},{q.z,"k"}}
        if q.x ~= 0 then
            s = string.format("%.3f",q.w)
        end
        for k,v in pairs(im) do
            if v[1] ~= 0 then
                if s then
                    if v[1] > 0 then
                        if v[1] == 1 then
                            s = s.." + "..v[2]
                        else
                            s = s.." + "..string.format("%.3f",v[1])..v[2]
                            
                        end
                    else
                        if v[1] == -1 then
                            s = s.." - "..v[2]
                        else
                            s = s.." - "..string.format("%.3f",-v[1])..v[2]
                        end
                    end
                else
                    if v[1] == 1 then
                        s = v[2]
                    elseif v[1] == - 1 then
                        s = "-" .. v[2]
                    else
                        s = string.format("%.3f",v[1]) .. v[2]
                    end
                end
            end
        end
        s = s or "0"
        return s
    end
    
    m["__concat"] = function (q,s)
        if is_a(s,"string") then
            return q:tostring() .. s
        else
            return q .. s:tostring()
        end
    end
    
    m["tomatrixleft"] = function (q)
        q = q:normalise()
        local a,b,c,d = q.w,q.x,q.y,q.z
        local ab,ac,ad,bb,bc,bd,cc,cd,dd = 2*a*b,2*a*c,2*a*d,2*b*b,2*b*c,2*b*d,2*c*c,2*c*d,2*d*d
        return matrix(
        1-cc-dd, bc-ad, ac+bd, 0,
        bc+ad, 1-bb-dd, cd-ab, 0,
        bd-ac, cd+ab, 1-bb-cc, 0,
        0,0,0,1
        )
    end
    
    m["tomatrixright"] = function (q)
        q = q:normalise()
        local a,b,c,d = q.w,-q.x,-q.y,-q.z
        local ab,ac,ad,bb,bc,bd,cc,cd,dd = 2*a*b,2*a*c,2*a*d,2*b*b,2*b*c,2*b*d,2*c*c,2*c*d,2*d*d
        return matrix(
        1-cc-dd, bc-ad, ac+bd, 0,
        bc+ad, 1-bb-dd, cd-ab, 0,
        bd-ac, cd+ab, 1-bb-cc, 0,
        0,0,0,1
        )
    end
    
    m["tomatrix"] = m["tomatrixright"]
    
    m["toangleaxis"] = function (q)
        q = q:normalise()
        local a = q.w
        q = vec3(q.x,q.y,q.z)
        if q == vec3(0,0,0) then
            return 0,vec3(0,0,1)
        end
        return 2*acos(a),q:normalise()
    end
    
    m["Gravity"] = function (q)
        local y = vec3(0,-1,0)^q
        return quat.fromToRotation(y,Gravity)*q
    end
    m.__extended = true
    
    for k,v in pairs(m) do
        rawset(mq,k,v)
    end
end

local exports = {
   qRotation = qRotation,
   qEuler = qEuler,
   qTangent = qTangent,
   qGravity = qGravity,
   quatGravity = quatGravity,
   qRotationRate = qRotationRate,
   quatRotationRate = quatRotationRate,
   modelMatrix = modelMatrix,
   applyMatrix = applyMatrix,
   viewMatrix = viewMatrix,
   projectionMatrix = projectionMatrix,
    resetMatrices = resetMatrices,
   rotate = rotate,
   translate = translate,
   scale = scale,
   camera = camera,
   setComplex = setComplex,
   edge = edge,
   smoothstep = smoothstep,
   smootherstep = smootherstep,
   line = line,
   ellipse = ellipse,
   rect = rect,
   sprite = sprite,
    readImage = readImage,
    image = image,
   text = text,
    clip = clip
}

if quat then
    extendQuat()
else
    exports["extendQuat"] = extendQuat
end

if cmodule then
   cmodule.export(exports)
else
   for k,v in pairs(exports) do
      _G[k] = v
   end
end
