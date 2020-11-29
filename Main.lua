-- DieRoll

function setup()
    --[[
    The quat userdata isn't available until the GL state has been initialised so we can't extend it before setup.
    This routine adds all the extensions to it now.
    --]]
    extendQuat()
    viewer.mode = FULLSCREEN
    --[[
    This section defines a texture for the die.  It is a single texture containing images for each of th4 sides.
    --]]
    local dieimg = image(600,100)
    setContext(dieimg)
    background(255, 255, 255, 255)
    noFill()
    stroke(200)
    strokeWidth(10)
    noSmooth()
    for k=1,6 do
        rect(100*(k-1)-5,-5,110,110)
    end
    noStroke()
    fill(200)
    for k=0,5 do
        for j=0,3 do
            rect(100*k+90*math.floor(j/2),90*(j%2),10,10)
        end
    end
    fill(255, 255, 255, 255)
    ellipseMode(RADIUS)
    for k=0,5 do
        for j=0,3 do
            ellipse(100*k+10+80*math.floor(j/2),10+80*(j%2),6)
        end
    end
    fill(0, 0, 0, 255)
    ellipseMode(CENTER)
    noStroke()
    -- fill(255, 0, 0, 255)
    ellipse(100*(5-1)+50,50,15)
    fill(0, 0, 0, 255)
    for k=1,2 do
        ellipse(100*(k-1)+50,50,15)
    end
    for _,k in ipairs({1,2,3,4,6}) do
        -- fill(255, 0, 0, 255)
        ellipse(100*(k-1)+25,25,15)
        fill(0, 0, 0, 255)
        ellipse(100*(k-1)+75,75,15)
    end
    for _,k in ipairs({1,4,6}) do
        ellipse(100*(k-1)+75,25,15)
        ellipse(100*(k-1)+25,75,15)
    end
    ellipse(525,50,15)
    ellipse(575,50,15)
    setContext()
    -- End of setting up the texture
    
    --[[
    I had a lot of code invested in meshes, so when Craft came along with its models then rather than ditch that code I adapted it to define models insteqd of meshes.  The simplest way was to define a class that mimiced a mesh in that it has the same attributes and methods but doesn't go to the bother of creating the underlying userdata.  Rather it gathers all the information and then at the end exports it to a model.
    --]]
    local __die = PseudoMesh()
    
    local number = 4
    
    local i,j,l,a
    a = {vec3(1,0,0),vec3(0,1,0),vec3(0,0,1)}
    --[[
    This loop defines the corners of the rounded cube.
    --]]
    for k=0,7 do
        i=2*(k%2)-1
        j=2*(math.floor(k/2)%2)-1
        l=2*math.floor(k/4)-1
        __die:addSphereSegment({
        startLatitude=0,
        endLatitude=90,
        startLongitude=0,
        endLongitude=90,
        axes={i*a[1],j*a[2],l*a[3]},
        solid=false,
        centre = i*a[1] + j*a[2] + l*a[3],
        radius = .3,
        number = 2*number,
        texOrigin = vec2(0,0),
        texSize = vec2(.01,.01)
        })
    end
    local tx = 0
    for l=1,3 do
        --[[
        This places the sides and the rounded edges.  It works in pairs, since opposite edges share a lot of code.
        The first loop does the edges, the second the faces.
        --]]
        for k=0,3 do
            j = 2*math.floor(k/2)-1
            i = -j*(2*(k%2)-1)
            __die:addCylinder({
            axes = a,
            centre = i*a[2] + j*a[3],
            height = 2,
            radius = .3,
            startAngle = k*90+180,
            deltaAngle = 90,
            faceted = false,
            size = number,
            texOrigin = vec2(0,0),
            texSize = vec2(.01,.01)
            })
        end
        for k=-1,1,2 do
            __die:addPolygon({
            vertices = {
            k*(1+.3)*a[1]+a[2]+a[3],
            k*(1+.3)*a[1]-a[2]+a[3],
            k*(1+.3)*a[1]-a[2]-a[3],
            k*(1+.3)*a[1]+a[2]-a[3]
            },
            viewFrom = -a[1],
            texCoords = {
                vec2(tx,0),
                vec2(tx+1/6,0),
                vec2(tx+1/6,1),
                vec2(tx,1)
            }
            })
            tx = tx + 1/6
        end
        table.insert(a,1,table.remove(a))
    end
    -- End of defining the rounded cube model
    
    --[[
    This part sets up the scene.  As with meshes, I had a lot of pre-Craft code for setting and manipulating the viewport.  The ViewCraft class adapted that for Craft.  It can be used with my touch handler to add natural moving and rotating of the camera.
    --]]
    scene = craft.scene()
    scene.camera:add(ViewCraft,nil,nil,{useGravity = false, eye = vec3(0,15,-5), up = vec3(0,0,-1), currentGravity = quat(1,0,0,0)})

    --[[
    Now we create our two entities based on the die model.
    --]]
    dieA = scene:entity()
    dieA.model = __die:toModel()
    local m = craft.material(asset.builtin.Materials.Standard)
    m.map = dieimg
    dieA.material = m
    dieA.position = vec3(-3,0,0)
    
    dieB = scene:entity()
    dieB.model = __die:toModel()
    local m = craft.material(asset.builtin.Materials.Standard)
    m.map = dieimg
    dieB.material = m
    dieB.position = vec3(3,0,0)
    
    --[[
    Our dice will rotate until the screen is tapped at which point they will rotate to show a particular face.
    --]]
    speed = 100 -- speed of rotation
    qa = quat(1,0,0,0) -- initial rotation of first die
    qb = quat(1,0,0,0) -- initial rotation of second die
    sla,sta = qpath(qa) -- this defines a path in rotation space for the first die
    slb,stb = qpath(qb) -- this defines a path in rotation space for the first die
    --[[
    When we want a die to show a particular value we need to rotate to that face.  These define the rotations that show each side.  The method 'rotateToquat' returns a quaternion that rotates the first vector to the second.  It's like the 'quat.fromToRotation' except that doesn't work in all cases.
    --]]
    sides = {
    vec3(0,-1,0):rotateToquat(vec3(0,1,0)),
    vec3(0,0,-1):rotateToquat(vec3(0,1,0)),
    vec3(1,0,0):rotateToquat(vec3(0,1,0)),
    vec3(0,0,1):rotateToquat(vec3(0,1,0)),
    vec3(-1,0,0):rotateToquat(vec3(0,1,0)),
    vec3(0,1,0):rotateToquat(vec3(0,1,0)),
    }
    
    --[[
    The program has three states:
    1. The dice are rotating aimlessly
    2. The dice rotate to show a given face and then stop
    3. The experiment runs repeatedly without rotations
    --]]
    state = 1
    
    --[[
    The program simulates a series of experiments, so keeps track of how many dice rolls meet the success criteria.  At the moment, it is counting doubles and computing the corresponding experimental probability.
    --]]
    trials = 0
    successes = 0
    trial = function(a,b) return a == b end
end

function draw()
    --[[
    Get the current rotations of the dice.
    --]]
    qa = sla(ElapsedTime)
    qb = slb(ElapsedTime)
    --[[
    What we do next depends on what state we're in
    --]]
    if state == 1 then
        --[[
        In state 1 we are freely rotating around so we just need to get a new path in rotation spacw when we reach the end of the current one.
        --]]
        if ElapsedTime > sta then
            sla,sta = qpath(qa)
        end
        if ElapsedTime > stb then
            slb,stb = qpath(qb)
        end
    elseif state == 3 then
        --[[
        In state 3 we run a new experiment each draw so choose new faces and rotate to show them and update our totals.
        --]]
        local n,m = math.random(1,6),math.random(1,6)
        --[[
        Having chosen the faces to show, we define the rotations to show them.  Once we show the right face, we can vary it a little by rotating about the forward facing axis.  This is purely aesthetic.
        --]]
        qa = quat.angleAxis(math.random(0,3)*90,vec3(0,1,0))*sides[n]
        qb = quat.angleAxis(math.random(0,3)*90,vec3(0,1,0))*sides[m]
        --[[
        Update our experiment totals.
        --]]
        if trial(n,m) then
            successes = successes + 1
        end
        trials = trials + 1
    end
    background(72, 55, 55, 255)
    -- update the rotations of the dice
    dieA.rotation = qa
    dieB.rotation = qb
    -- update and draw the scene
    scene:update(DeltaTime)
    scene:draw()
    
    -- reset the view so that we go back to 2D mode for adding text
    viewMatrix(matrix())
    ortho()
    pushStyle()
    fill(255, 255, 255, 255)
    fontSize(30)
    textMode(CORNER)
    --[[
    This set of commands writes some useful stuff on the screen about our experiments
    --]]
    local tw,th,a,lh
    a = 100
    lh = 150
    text("Trials:",a,lh)
    tw,th = textSize("Trials: ")
    a = a + tw
    text(trials,a,lh)
    tw,th = textSize("100000")
    a = a + tw
    text("Successes:",a,lh)
    tw,th = textSize("Successes: ")
    a = a + tw
    text(successes,a,lh)
    tw,th = textSize("100000")
    a = a + tw
    text("Probability:",a,lh)
    tw,th = textSize("Probability: ")
    a = a + tw
    text(math.floor(successes/math.max(1,trials)*10000)/10000,a,lh)
    --]]
    -- [[
    tw,th = textSize("100000")
    a = a + tw
    text("FPS:",a,lh)
    tw,th = textSize("FPS: ")
    a = a + tw
    text(math.floor(1/DeltaTime),a,lh)
    --]]
    popStyle()
end

function touched(t)
    if t.state == ENDED then
        if t.tapCount == 2 then
            --[[
            A double tap switches between the single experiment mode and the multiple experiment one
            --]]
            if state == 3 then
                state = 2
            else
                state = 3
            end
        else
            if state == 1 then
                --[[
                A single tap in state 1 (freely rotating) starts us rotating to show a given face
                --]]
                local n,m = math.random(1,6),math.random(1,6) -- pick a face for each die
                -- define a path of rotations from our current rotation to one that shows the selected face
                sla,sta = qpath(qa,quat.angleAxis(math.random(0,3)*90,vec3(0,1,0))*sides[n])
                slb,stb = qpath(qb,quat.angleAxis(math.random(0,3)*90,vec3(0,1,0))*sides[m])
                -- when both faces are shown, update the information for display
                tween.delay(math.max(sta,stb) - ElapsedTime,function()
                    if trial(n,m) then
                        successes = successes + 1
                    end
                    trials = trials + 1
                end)
                state = 2
            elseif state == 2 then
                -- If we're in state 2, start feely rotating again
                sla,sta = qpath(qa)
                slb,stb = qpath(qb)
                state = 1
            end
        end
    end
end

--[[
This function defines a path in the space of rotations from a given starting point to an ending point.  If the ending point isn't given, one is chosen at random.  It returns a function that defines the path and the length of time that path will take (this keeps the rotation rate constant and means that a path between nearby rotations will be quicker than between far away ones).
--]]
function qpath(q,qt)
    -- If a target isn't given, pick one at random
    qt = qt or quat.angleAxis(360*math.random(),RandomVec3())
    -- Work out the length of the path
    local s = math.acos(q:dot(qt))/2
    -- 'slerp' stands for spherical interpolation
    local sl = q:make_slerp(qt)
    local st = ElapsedTime
    return function(t) return sl(math.min(1,(t-st)/s)) end, st + s
end


--[[
Small utility function that picks a unit vec3 at random, uniformly distributed on the sphere.
--]]
function RandomVec3()
    local th = 2*math.pi*math.random()
    local z = 2*math.random() - 1
    local r = math.sqrt(1 - z*z)
    return vec3(r*math.cos(th),r*math.sin(th),z)
end

