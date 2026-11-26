"""Render a two-handled surface and its depth-tested transverse meridian curves."""
import json
import math
from pathlib import Path

import numpy as np
from PIL import Image


def build(directory):
    directory = Path(directory)
    directory.mkdir(parents=True,exist_ok=True)
    width,height,scale = 1120,570,220
    tilt,roll = .81,-.075
    ct,st,cr,sr = math.cos(tilt),math.sin(tilt),math.cos(roll),math.sin(roll)

    def field(x,y,z):
        a=np.hypot(np.hypot(x+1.02,y)-.93,z)-.38
        b=np.hypot(np.hypot(x-1.02,y)-.93,z)-.38
        blend=np.clip(.5+.5*(b-a)/.54,0,1)
        return (1-blend)*b+blend*a-.54*blend*(1-blend)

    yy,xx=np.mgrid[:height,:width].astype(np.float32)
    u,v=(xx-width/2)/scale,(yy-height/2)/scale
    x,vertical=cr*u+sr*v,-sr*u+cr*v
    depth=np.full_like(x,3.0)
    visible=np.ones_like(x,dtype=bool)
    for _ in range(86):
        y,z=-ct*vertical-st*depth,-st*vertical+ct*depth
        dist=field(x,y,z)
        visible &= (dist>.0008)&(depth>-3.0)
        if not visible.any():
            break
        depth[visible]-=np.minimum(dist[visible],.48)
    hit=depth>-3.0
    y,z=-ct*vertical-st*depth,-st*vertical+ct*depth
    h=.002
    nx=(field(x+h,y,z)-field(x-h,y,z))/(2*h)
    ny=(field(x,y+h,z)-field(x,y-h,z))/(2*h)
    nz=(field(x,y,z+h)-field(x,y,z-h))/(2*h)
    key=np.maximum(0,-.50*nx-.33*ny+.80*nz)
    rim=(1-np.clip(-st*ny+ct*nz,0,1))**3
    lit=.19+.71*key+.10*rim
    rgb=np.clip(np.array([5,12,26])+lit[...,None]*np.array([72,137,172])
                +rim[...,None]*np.array([12,24,29]),0,255).astype('uint8')
    rgba=np.dstack((rgb,np.where(hit,255,0).astype('uint8')))
    Image.fromarray(rgba).save(directory/'double-torus.png')
    data=[]
    for center,angle in [(-1.02,math.pi+.58),(1.02,-.60)]:
        pieces=[]
        current=[]
        for k in range(401):
            phi=2*math.pi*(k/400+.075)
            X=center+(.93+.384*math.cos(phi))*math.cos(angle)
            Y=(.93+.384*math.cos(phi))*math.sin(angle)
            Z=.384*math.sin(phi)
            vertical=-ct*Y-st*Z
            U=width/2+scale*(cr*X-sr*vertical)
            V=height/2+scale*(sr*X+cr*vertical)
            if -st*Y+ct*Z>=depth[round(V),round(U)]-.042:
                current.append([(U-width/2)/width,(height/2-V)/width])
            elif current:
                if len(current)>1:
                    pieces.append(current)
                current=[]
        if len(current)>1:
            pieces.append(current)
        data.append(pieces)
    (directory/'surface-paths.json').write_text(json.dumps(data),encoding='utf8')
