"""Manim Community scenes for Six moves on a double torus."""
import json
import os
from pathlib import Path

import av
import numpy as np
import manimpango
from manim import (
    Circle, Create, DashedLine, Dot, FadeIn, FadeOut, GrowFromCenter,
    Group, ImageMobject, Indicate, LaggedStart, Line, Polygon, Rectangle,
    Scene, SurroundingRectangle, Text, Transform, TransformFromCopy, VGroup,
    VMobject, ValueTracker, always_redraw, config, linear, smooth,
)

BG='#0C1422'
WHITE='#F3F0E8'
MUTED='#B2C3CF'
LINE='#496276'
DARK='#233747'
AQUA='#55E3CE'
CORAL='#FF987B'
GOLD='#F2CC76'
BLUE='#85B7F2'
FONTS=set(manimpango.list_fonts())
SERIF=next((s for s in ('Georgia','Liberation Serif','DejaVu Serif') if s in FONTS),'serif')
SANS=next((s for s in ('Segoe UI','DejaVu Sans','Liberation Sans') if s in FONTS),'sans')
DATA=Path(os.environ.get('CURVE_FILM_DATA',Path(__file__).parent))
FPS=30


def pos(x,y):
    return np.array([x,y,0.0])


def words(value,x,y,size=33,color=WHITE,serif=False,italic=False):
    return Text(str(value),font=SERIF if serif else SANS,font_size=size,color=color,
                slant='ITALIC' if italic else 'NORMAL',disable_ligatures=True).move_to(pos(x,y))


def stroke(p,q,color=LINE,width=4):
    return Line(p,q,color=color,stroke_width=width)


def dot(p,color=AQUA,r=.085):
    return Dot(p,radius=r,color=color)


def label(value,p,color=AQUA):
    return words(value,p[0],p[1]-.44,28,color,serif=True,italic=True)


def strip_title(value):
    t=words(value,0,3.12,45,serif=True)
    t.to_edge(np.array([-1.,0,0]),buff=.74)
    return t


def source(value):
    return words(value,0,-2.94,20,MUTED)


def crossing_order(permutation):
    xs=np.linspace(-4.55,5.55,len(permutation))
    rows=VGroup()
    marked=[]
    for name,values,y,color in [('along a',range(1,len(xs)+1),.55,AQUA),
                                ('along b',permutation,-.40,CORAL)]:
        row=VGroup(words(name,-5.72,y,23,MUTED,True,True))
        for x,value in zip(xs,values):
            number=words(str(value).replace('-','−'),x,y,26,color)
            row.add(number)
            if abs(value)==8:
                marked.append(number)
        rows.add(row)
    rings=VGroup(*(Circle(radius=.29,color=GOLD,stroke_width=2).move_to(number) for number in marked))
    return rows,rings


def path(points,color,width=5):
    m=VMobject(color=color,stroke_width=width)
    m.set_points_as_corners(points)
    return m


def make_surface(where,width):
    shape=ImageMobject(str(DATA/'double-torus.png')).scale_to_fit_width(width).move_to(where)
    curves=[]
    for pieces,color in zip(json.loads((DATA/'surface-paths.json').read_text()),[AQUA,CORAL]):
        curves.append(VGroup(*(path([where+pos(width*u,width*v) for u,v in piece],color,6) for piece in pieces)))
    return shape,curves


class Timed(Scene):
    def setup(self):
        self.camera.background_color=BG
        schedule=json.loads((DATA/'timing.json').read_text(encoding='utf8'))
        self.plan=schedule['scenes'][type(self).__name__]
        self.beats={item['id']:item for item in self.plan['beats']}
        self.part_frames={}
        if config.frame_rate!=FPS:
            raise ValueError('The authored sequence requires 30 fps.')

    def elapsed_frames(self):
        # Cached plays advance Cairo's clock by the requested duration. The
        # encoder may have rounded that play up to the next whole frame.
        total=0
        for part in self.renderer.file_writer.partial_movie_files:
            if part not in self.part_frames:
                with av.open(str(part)) as clip:
                    self.part_frames[part]=clip.streams.video[0].frames
            total+=self.part_frames[part]
        return total

    def wait_to(self,frame):
        now=self.elapsed_frames()
        if frame>now:
            self.wait((frame-now+.001)/FPS,frozen_frame=True)

    def cue(self,name,fraction=0):
        beat=self.beats[name]
        self.wait_to(round(beat['start']+fraction*(beat['end']-beat['start'])))

    def finish(self):
        if self.elapsed_frames()>self.plan['frames']:
            raise ValueError(f'{type(self).__name__} exceeds its narration timeline.')
        self.wait_to(self.plan['frames'])


class Opening(Timed):
    def construct(self):
        heading=strip_title('Six moves on a double torus')
        body,(curve_a,curve_b)=make_surface(pos(-2.45,-.07),8.4)
        self.add(heading,body)
        q=words('One twist',3.9,.4,51,serif=True)
        sub=words('How many moves?',3.9,-.48,31,AQUA)
        self.play(FadeIn(q,shift=pos(0,.18)),FadeIn(sub),run_time=.95)
        self.play(Create(curve_a),run_time=1.15)
        self.cue('edge')
        self.play(FadeOut(q),FadeOut(sub),Create(curve_b),run_time=.95)
        p0,p1=pos(2.1,.1),pos(5.3,.1)
        n0,n1=dot(p0,AQUA,.13),dot(p1,CORAL,.13)
        self.play(TransformFromCopy(curve_a,n0),TransformFromCopy(curve_b,n1),run_time=1)
        self.play(Create(stroke(p0,p1,WHITE,3)),FadeIn(words('one edge',3.7,-.60,30,WHITE,True)),
                  FadeIn(source('Two disjoint loops on different handles')),run_time=.85)
        self.cue('challenge')
        old=Group(*[m for m in self.mobjects if m is not heading])
        self.play(FadeOut(old),Transform(heading,strip_title('Could five moves be enough?')),run_time=.6)
        pts=[pos(-5.45+i*1.81,-.23+.16*np.cos(i*np.pi/3)) for i in range(7)]
        chain=VGroup(*(stroke(a,b,AQUA if i<3 else CORAL,5) for i,(a,b) in enumerate(zip(pts,pts[1:]))))
        nodes=VGroup(*(dot(p,GOLD if i==3 else WHITE) for i,p in enumerate(pts)))
        self.play(LaggedStart(*(Create(s) for s in chain),lag_ratio=.17),
                  LaggedStart(*(GrowFromCenter(n) for n in nodes),lag_ratio=.16),run_time=1.65)
        self.cue('challenge',.47)
        upper=[(1-t)*pts[0]+t*pts[-1]+pos(0,1.55*np.sin(np.pi*t)) for t in np.linspace(0,1,6)]
        possible=VGroup(*(DashedLine(a,b,dash_length=.13,color=GOLD,stroke_width=2.5)
                          for a,b in zip(upper,upper[1:])),*(dot(p,GOLD,.07) for p in upper[1:-1]))
        self.play(Create(possible),FadeIn(words('a possible shortcut',0,1.86,26,GOLD)),run_time=1.2)
        self.finish()


class Collar(Timed):
    def construct(self):
        title=strip_title('A distance-four starting pair')
        self.add(title)
        rows,rings=crossing_order([1,-8,-3,-10,5,6,7,-2,-9,-4,11,12])
        legend=words('Number the crossings along a. Read the signed labels along b.',0,-1.68,25,MUTED)
        caption=source('Starting diagram  ·  Birman, Margalit & Menasco, Figure 1')
        self.play(FadeIn(legend),FadeIn(caption),FadeIn(rows[0],shift=pos(.16,0)),run_time=.58)
        self.play(FadeIn(rows[1],shift=pos(.16,0)),Create(rings),run_time=.7)
        initial=VGroup(rows,rings,legend,caption)
        self.cue('strip')
        self.play(FadeOut(initial),Transform(title,strip_title('What one turn does')),run_time=.45)
        left,right,low,high=-4.8,4.8,-1.45,1.45
        w=right-left
        box=Rectangle(width=w,height=high-low,color=LINE,stroke_width=2,fill_color=DARK,fill_opacity=.26)
        core=DashedLine(pos(left,0),pos(right,0),dash_length=.14,color=GOLD,stroke_width=2)
        fixed=[.15,.45,.75]
        strands=VGroup(*(stroke(pos(left+w*u,low),pos(left+w*u,high),AQUA,3) for u in fixed))
        tags=VGroup(words('cut',left,-1.87,22,MUTED),words('same cut',right,-1.87,22,MUTED),
                    words('B',right+.38,0,27,GOLD,True,True))
        self.play(Create(box),Create(core),LaggedStart(*(Create(s) for s in strands),lag_ratio=.15),
                  FadeIn(tags),run_time=1.1)
        self.play(FadeIn(source('Three representative strands of the twelve')),run_time=.45)
        phase=ValueTracker(0.)
        def winding():
            pieces=VGroup()
            turns=phase.get_value()
            for u in fixed:
                u+=.028
                cuts=[0.,1.]
                if turns>1e-8:
                    cuts[1:1]=[(k-u)/turns for k in range(1,4) if 0<(k-u)/turns<1]
                for a,b in zip(cuts,cuts[1:]):
                    period=np.floor(u+turns*(a+b)/2)
                    start=pos(left+w*(u+turns*a-period),low+(high-low)*a)
                    end=pos(left+w*(u+turns*b-period),low+(high-low)*b)
                    pieces.add(stroke(start,end,CORAL,4))
            return pieces
        moving=always_redraw(winding)
        self.add(moving)
        self.cue('turn')
        self.play(phase.animate.set_value(1),rate_func=smooth,run_time=3.5)
        self.cue('products')
        count=words('12 × 12 = 144',0,2.02,34,GOLD,True)
        self.play(FadeIn(count),run_time=.6)
        self.cue('products',.56)
        self.play(phase.animate.set_value(2),Transform(count,words('2 × 12 × 12 = 288',0,2.02,34,GOLD,True)),
                  rate_func=smooth,run_time=2.2)
        self.cue('mahan')
        moving.clear_updaters()
        old=Group(*[m for m in self.mobjects if m is not title])
        self.play(FadeOut(old),Transform(title,strip_title('The marked twelve-crossing pair')),run_time=.58)
        row1=VGroup(words('one twist',-2.25,.5,38,MUTED),words('5 moves',2.40,.5,48,AQUA,True))
        row2=VGroup(words('two twists',-2.25,-.85,38,MUTED),words('?',2.40,-.85,54,GOLD,True))
        self.play(FadeIn(row1),FadeIn(source('Mahanta, distance-five example, §6')),run_time=.75)
        self.cue('mahan',.58)
        self.play(FadeIn(row2,shift=pos(0,.16)),run_time=.7)
        self.finish()


class Fold(Timed):
    def construct(self):
        self.add(strip_title('Build the six-edge route'))
        points=[pos(-5.55,0),pos(-3.7,0),pos(-1.85,0),pos(0,0)]
        core=pos(.85,1.60)
        edges=VGroup(*(stroke(a,b,AQUA,6) for a,b in zip(points,points[1:])))
        nodes=VGroup(*(dot(p,AQUA if i!=3 else GOLD,.11) for i,p in enumerate(points)))
        labs=VGroup(*(label(v,p,GOLD if i==3 else AQUA) for i,(v,p) in enumerate(zip(['a','u','v','w'],points))))
        b=VGroup(dot(core,WHITE,.10),words('b',core[0]+.32,core[1]+.07,30,WHITE,True,True))
        stem=DashedLine(points[-1],core,color=MUTED,dash_length=.115,stroke_width=3)
        self.play(LaggedStart(*(Create(e) for e in edges),lag_ratio=.25),FadeIn(nodes),FadeIn(labs),run_time=1.6)
        self.play(Create(stem),FadeIn(b),run_time=.75)
        self.cue('pivot')
        ring=Circle(radius=.26,color=GOLD,stroke_width=3).move_to(points[-1])
        remark=words('The twist fixes w.',0,-1.52,34,GOLD,True)
        self.play(Create(ring),FadeIn(remark),run_time=.95)
        self.cue('reflect')
        self.play(FadeOut(remark),run_time=.45)
        goal=[points[-1],pos(1.85,0),pos(3.7,0),pos(5.55,0)]
        mirrored=VGroup(*(stroke(a,b,CORAL,6) for a,b in zip(goal,goal[1:])))
        self.play(TransformFromCopy(edges,mirrored,path_arc=-.8),run_time=1.55)
        names=['Tv','Tu','Ta']
        for i,p in enumerate(goal[1:]):
            self.play(GrowFromCenter(dot(p,CORAL,.11)),FadeIn(label(names[i],p,CORAL)),run_time=.28)
        trace=dot(points[0],WHITE,.14)
        self.add(trace)
        for p in points[1:]+goal[1:]:
            self.play(trace.animate.move_to(p),rate_func=linear,run_time=.22)
        self.remove(trace)
        self.cue('upper')
        self.play(FadeIn(words('3  +  3  =  6',0,-1.78,52,WHITE,True)),
                  FadeIn(source('An upper bound on the distance')),run_time=.8)
        self.finish()


class Bounds(Timed):
    def construct(self):
        title=strip_title('When the collar can rule out shortcuts')
        self.add(title)
        track_y=.05
        ticks=[pos(-4.8+1.6*j,track_y) for j in range(7)]
        axis=VGroup(stroke(ticks[0],ticks[-1],LINE,3),
                    *(stroke(p+pos(0,-.14),p+pos(0,.14),MUTED,3) for p in ticks),
                    *(words(str(i),p[0],track_y-.52,25,MUTED) for i,p in enumerate(ticks)))
        self.play(Create(axis),FadeIn(words('Distance in the annular cover',0,1.73,30,MUTED)),run_time=1.25)
        pointer=dot(ticks[0],AQUA,.12)
        self.add(pointer)
        self.cue('track',.54)
        self.play(pointer.animate.move_to(ticks[1]),run_time=.6)
        self.play(pointer.animate.move_to(ticks[2]),run_time=.6)
        self.cue('six')
        length=stroke(ticks[0],ticks[6],GOLD,6)
        self.play(Create(length),pointer.animate.move_to(ticks[6]),
                  FadeIn(words('4 twists  ·  gap 6',0,-1.75,38,GOLD,True)),run_time=1.25)
        self.cue('miss')
        old=Group(*[m for m in self.mobjects if m is not title])
        self.play(FadeOut(old),run_time=.42)
        a,z,t,b=pos(-4.4,-.18),pos(0,-.18),pos(4.4,-.18),pos(0,1.52)
        self.play(Create(DashedLine(z,b,color=MUTED,dash_length=.1)),
                  FadeIn(VGroup(dot(b,WHITE),label('b',b,WHITE),dot(z,GOLD,.13),label('z',z,GOLD),
                                dot(a,AQUA,.12),label('a',a),dot(t,CORAL,.12),label('Ta',t,CORAL))),
                  run_time=.8)
        self.cue('miss',.40)
        self.play(Create(stroke(a,z,AQUA,5)),Create(stroke(z,t,CORAL,5)),
                  FadeIn(words('≥ 3',-2.2,.3,38,AQUA,True)),FadeIn(words('≥ 3',2.2,.3,38,CORAL,True)),
                  FadeIn(source('A vertex disjoint from b is at most one edge from it.')),run_time=.85)
        self.cue('gap')
        old=Group(*[m for m in self.mobjects if m is not title])
        self.play(FadeOut(old),run_time=.45)
        self.play(FadeIn(axis),FadeIn(stroke(ticks[0],ticks[4],GOLD,6)),FadeIn(dot(ticks[4],GOLD,.13)),
                  FadeIn(words('2 twists  ·  gap 4',0,1.70,41,GOLD,True)),run_time=.75)
        self.cue('gap',.47)
        self.play(FadeIn(words('A five-edge path still has room.',0,-1.67,32,WHITE)),run_time=.68)
        self.finish()


def textbook_triangle():
    top,left,right=pos(-.3,1.48),pos(-3.45,-1.56),pos(2.86,-1.56)
    border=Polygon(top,left,right,stroke_color=MUTED,stroke_width=3,fill_color=DARK,fill_opacity=.24)
    def lerp(p,q,t):
        return (1-t)*p+t*q
    lhs=[lerp(top,left,t) for t in (.26,.51,.79)]
    rhs=[lerp(top,right,t) for t in (.26,.51)]
    base=lerp(left,right,.20)
    strands=VGroup(stroke(lhs[0],rhs[0],AQUA,5),stroke(lhs[1],rhs[1],AQUA,5),stroke(lhs[2],base,CORAL,5))
    endpoints=VGroup(*(dot(p,WHITE,.074) for p in [*lhs,*rhs,base]))
    tags=VGroup(words('3',-2.52,.33,40,GOLD,True),words('2',1.99,.33,40,GOLD,True),
                words('1',-.32,-2.01,40,GOLD,True))
    return border,strands,endpoints,tags


class Search(Timed):
    def construct(self):
        title=strip_title('Turn the shortcut into a finite test')
        self.add(title)
        tri,strands,ends,weights=textbook_triangle()
        self.play(Create(tri),FadeIn(weights),run_time=.9)
        self.cue('triangle',.46)
        self.play(LaggedStart(*(Create(s) for s in strands),lag_ratio=.25),FadeIn(ends),run_time=1.4)
        self.cue('bounded')
        self.play(VGroup(tri,strands,ends,weights).animate.scale(.62).shift(pos(-3.0,.14)),run_time=.75)
        right=VGroup(words('Bound the crossings',2.55,.76,37,AQUA,True),
                     words('Enumerate the first moves',2.55,-.18,28,MUTED))
        cite=source('Efficient geodesics  ·  Birman, Margalit & Menasco, Theorem 1.1')
        self.play(FadeIn(right,shift=pos(.2,0)),FadeIn(cite),run_time=.85)
        self.cue('tree')
        old=Group(*[m for m in self.mobjects if m is not title])
        self.play(FadeOut(old),run_time=.45)
        rows=[[pos(-2.9,1.38)], [pos(-4.7+1.8*i,.51) for i in range(3)],
              [pos(-5.45+.9*i,-.38) for i in range(7)],
              [pos(-5.7+.4*i,-1.30) for i in range(15)]]
        self.add(dot(rows[0][0],GOLD,.12))
        levels=[]
        for k,c in enumerate([AQUA,BLUE,CORAL],1):
            oldrow,newrow=rows[k-1],rows[k]
            fan=VGroup()
            for i,p in enumerate(newrow):
                parent=oldrow[min(len(oldrow)-1,int(i*len(oldrow)/len(newrow)))]
                fan.add(stroke(parent,p,LINE,2),dot(p,c,.07))
            levels.append(fan)
        stats=[('80','candidate first moves'),('2,336','next tests'),('14,016','terminal tests')]
        for i,((number,unit),fan) in enumerate(zip(stats,levels)):
            self.cue('tree',[.04,.38,.64][i])
            y=1.05-i*1.04
            self.play(Create(fan),FadeIn(words(number,1.82,y,43,[AQUA,BLUE,CORAL][i],True)),
                      FadeIn(words(unit,4.29,y,24,MUTED)),run_time=.72)
        self.cue('fill')
        self.play(FadeIn(source('All terminal pairs fill the surface.')),run_time=.56)
        self.cue('fill',.45)
        self.play(Indicate(levels[-1],color=GOLD,scale_factor=1.05),run_time=.9)
        self.cue('spectrum')
        old=Group(*[m for m in self.mobjects if m is not title])
        self.play(FadeOut(old),Transform(title,strip_title('The exact answer for Figure 18')),run_time=.5)
        for i,(a,b,col) in enumerate([('1 twist','5',AQUA),('2 twists','6',GOLD),('3 or more','6',GOLD)]):
            x=-4.05+4.05*i
            self.play(FadeIn(words(a,x,1.06,28,MUTED)),FadeIn(words(b,x,-.15,94,col,True)),
                      FadeIn(words('moves',x,-1.28,26,MUTED)),run_time=.42)
        self.finish()


class Census(Timed):
    def construct(self):
        title=strip_title('How small can the starting pair be?')
        self.add(title)
        main=words('One twist',0,.5,64,CORAL,True)
        sub=words('Starting distance 4',0,-.72,32,MUTED)
        self.play(FadeIn(main,shift=pos(0,.19)),FadeIn(sub),run_time=.85)
        self.cue('twelve')
        self.play(FadeOut(main),FadeOut(sub),run_time=.42)
        titles=VGroup(words('starting crossings',-4.48,1.72,22,MUTED),
                      words('ordered starting pairs',.18,1.72,22,MUTED),
                      words('after one twist',4.64,1.72,22,MUTED))
        self.play(FadeIn(titles),run_time=.4)
        def row(n,y,count,outcome,col):
            count_label=words(str(n),-4.48,y,52,WHITE,True)
            dots=VGroup(*(Circle(radius=.095,stroke_color=col,stroke_width=3,
                                  fill_color=col,fill_opacity=.24).move_to(pos(.12+(i-(count-1)/2)*.40,y))
                           for i in range(count)))
            outcome_label=words(outcome,4.64,y,34,col,True)
            self.play(FadeIn(count_label),LaggedStart(*(GrowFromCenter(d) for d in dots),lag_ratio=.14),
                      run_time=1.25)
            self.play(FadeIn(outcome_label),run_time=.48)
            return VGroup(count_label,dots,outcome_label)
        row(12,.85,5,'all 5',AQUA)
        self.cue('thirteen')
        row(13,-.10,11,'all 5',AQUA)
        take=source('Minimum intersection is sufficient in genus two. Thirteen crossings also work for five.')
        self.cue('thirteen',.49)
        self.play(FadeIn(take),run_time=.65)
        self.cue('fourteen')
        self.play(FadeOut(take),run_time=.34)
        r14=words('14',-4.48,-1.14,52,GOLD,True)
        one=words('one explicit example',.12,-1.14,27,MUTED)
        dist=words('6 moves',4.64,-1.14,36,GOLD,True)
        self.play(FadeIn(r14),FadeIn(one),FadeIn(dist),run_time=.86)
        self.cue('fourteen',.52)
        self.play(FadeIn(words('14² = 196 endpoint crossings',0,-2.25,34,GOLD,True)),run_time=.7)
        self.cue('min')
        highlight=SurroundingRectangle(VGroup(r14,one,dist),color=GOLD,buff=.18,stroke_width=2)
        self.play(Create(highlight),run_time=.65)
        self.cue('min',.22)
        old=Group(*[m for m in self.mobjects if m is not title])
        self.play(FadeOut(old),Transform(title,strip_title('The fourteen-crossing witness')),run_time=.48)
        rows,_=crossing_order([1,-9,-3,-11,-5,-6,-7,-8,-2,-10,-4,12,13,14])
        self.play(LaggedStart(*(FadeIn(row,shift=pos(.13,0)) for row in rows),lag_ratio=.35),
                  FadeIn(words('One twist   ·   Six moves   ·   196 endpoint crossings',0,-1.77,31,GOLD,True)),run_time=.8)
        self.finish()


class AnyDistance(Timed):
    def construct(self):
        title=strip_title('What about seven moves?')
        self.add(title)
        ref=source('Earlier constructions  ·  Schleimer (2006)  ·  Ido, Jang & Kobayashi (2012)  ·  Aougab & Taylor (2013)')
        self.play(FadeIn(ref),run_time=.55)
        points=[pos(-5.7+1.14*i,.0) for i in range(11)]
        chain=VGroup(*(stroke(points[i],points[i+1],AQUA if i<4 else CORAL,5) for i in range(10)))
        nodes=VGroup(*(dot(p,WHITE,.085) for p in points))
        self.play(LaggedStart(*(Create(e) for e in chain[:4]),lag_ratio=.18),FadeIn(nodes[:5]),run_time=1.15)
        number=words('length 4',0,1.37,38,AQUA,True)
        self.play(FadeIn(number),run_time=.48)
        self.cue('grow')
        self.play(LaggedStart(*(Create(e) for e in chain[4:6]),lag_ratio=.23),FadeIn(nodes[5:7]),
                  Transform(number,words('length 6',0,1.37,38,CORAL,True)),run_time=1.1)
        self.cue('grow',.54)
        self.play(LaggedStart(*(Create(e) for e in chain[6:]),lag_ratio=.18),FadeIn(nodes[7:]),
                  Transform(number,words('length 10',0,1.37,38,CORAL,True)),run_time=1.1)
        self.cue('seven')
        highlight=VGroup(*(stroke(points[i],points[i+1],GOLD,7) for i in range(7)))
        self.play(Create(highlight),FadeIn(Circle(radius=.22,color=GOLD).move_to(points[7])),
                  FadeIn(words('7',points[7][0],-.65,38,GOLD,True)),run_time=1.3)
        self.cue('close')
        old=Group(*self.mobjects)
        self.play(FadeOut(old),run_time=.45)
        closing=strip_title('Exactly six')
        self.add(closing)
        self.play(FadeIn(words('Mahanta’s 12-crossing pair',-2.15,.67,32,MUTED)),
                  FadeIn(words('2 turns',3.66,.67,47,AQUA,True)),run_time=.65)
        self.cue('close',.52)
        self.play(FadeIn(words('Smallest one-twist seed',-2.15,-.55,32,MUTED)),
                  FadeIn(words('14 crossings',3.66,-.55,47,GOLD,True)),
                  FadeIn(source('Short Dehn twists on the closed genus-two surface')),run_time=.8)
        self.finish()


class Minimum(Timed):
    def construct(self):
        title=strip_title('How few crossings can six moves take?')
        self.add(title)

        def at(n):
            return -5.5+11*n/200

        def scale():
            axis=stroke(pos(at(0),-.10),pos(at(200),-.10),LINE,3)
            marks=VGroup(*(stroke(pos(at(n),-.23),pos(at(n),.03),LINE,3)
                           for n in range(0,201,10)))
            return VGroup(axis,marks,words('0',at(0),-.56,22,MUTED),
                          words('crossings',0,-.75,23,MUTED))

        ruler=scale()
        twist=VGroup(dot(pos(at(196),-.1),CORAL,.12),words('196',at(196),.54,40,CORAL,True),
                     words('one twist',at(196),1.12,23,MUTED))
        self.play(Create(ruler),FadeIn(twist),run_time=1.15)
        self.cue('bands')
        self.play(FadeOut(ruler),FadeOut(twist),Transform(title,strip_title('Six bands after cutting')),
                  run_time=.54)
        weights=[30,30,6,6,30,30]
        xs=np.linspace(-4.85,4.85,6)
        bundles=VGroup()
        for x,w in zip(xs,weights):
            offsets=(np.arange(w)-(w-1)/2)*.041
            strands=VGroup(*(stroke(pos(x+t,-.53),pos(x+t+.13,.67),AQUA,1.5) for t in offsets))
            bundles.add(VGroup(strands,words(w,x,-1.12,38,WHITE,True)))
        self.play(LaggedStart(*(FadeIn(b,shift=pos(0,.15)) for b in bundles),lag_ratio=.18),
                  run_time=1.65)
        self.cue('glue')
        total=words('30 + 30 + 6 + 6 + 30 + 30 = 132',0,-2.26,36,GOLD,True)
        self.play(FadeIn(total),run_time=.55)
        self.cue('glue',.27)
        self.play(FadeOut(bundles),FadeOut(total),Transform(title,strip_title('Shift the boundary by 13 places')),
                  run_time=.55)
        xs=np.linspace(-4.65,4.65,6)
        top=VGroup(*(words(j,x,.75,33,WHITE,True) for j,x in enumerate(xs)))
        bot=VGroup(*(words(j+13,x,-.72,33,AQUA,True) for j,x in enumerate(xs)))
        seams=VGroup(*(stroke(pos(x,.46),pos(x,-.42),LINE,3) for x in xs))
        self.play(FadeIn(top),FadeIn(bot,shift=pos(.7,0)),
                  LaggedStart(*(Create(s) for s in seams),lag_ratio=.16),run_time=1.25)
        self.play(FadeIn(words('Boundary positions, read modulo 132',0,-1.68,24,MUTED)),
                  run_time=.45)
        self.cue('lower')
        old=Group(*[m for m in self.mobjects if m is not title])
        self.play(FadeOut(old),Transform(title,strip_title('Could a smaller diagram work?')),run_time=.55)
        ruler=scale()
        line=stroke(pos(at(0),-.1),pos(at(131),-.1),AQUA,8)
        attained=VGroup(dot(pos(at(132),-.1),GOLD,.14),words('132',at(132),.55,44,GOLD,True))
        self.play(Create(ruler),FadeIn(attained),run_time=.82)
        self.cue('lower',.31)
        self.play(Create(line),run_time=1.6)
        self.play(FadeIn(words('0–131 crossings',-2.15,1.08,32,AQUA,True)),
                  FadeIn(words('Every pair has a path of at most five moves.',0,-1.89,29,WHITE)),
                  run_time=.75)
        self.cue('result')
        old=Group(*self.mobjects)
        self.play(FadeOut(old),run_time=.45)
        self.add(strip_title('Minimum crossings on the double torus'))
        self.play(FadeIn(words('Five moves',-3.18,.92,34,MUTED)),
                  FadeIn(words('40',-3.18,-.34,87,AQUA,True)),run_time=.7)
        self.cue('result',.46)
        self.play(FadeIn(words('Six moves',3.18,.92,34,MUTED)),
                  FadeIn(words('132',3.18,-.34,87,GOLD,True)),run_time=.7)
        self.finish()


class Poster(Scene):
    def construct(self):
        self.camera.background_color=BG
        body,(a,b)=make_surface(pos(-2.55,-.36),8.3)
        self.add(strip_title('Six moves on a double torus'),body,a,b,
                 words('A disjoint pair on the double torus',-2.55,-2.58,20,MUTED),
                 words('14',3.92,.63,118,GOLD,True),words('starting crossings',3.92,-.72,29,MUTED),
                 words('One twist gives distance six.',3.75,-1.52,26,WHITE,True))
