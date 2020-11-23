/*
 * xs-school-mainpage.js
 *
 * Libraries in use:
 *
 * async-script-loader:
 *  https://github.com/CSharperMantle/async-script-loader
 *  MIT License. Copyright (c) Rong "Mantle" Bao (aka CSharperMantle)
 * Click-switch Images:
 *  https://codepen.io/CSharperMantle/pen/yLOrJQQ
 *  MIT License. Copyright (c) Rong "Mantle" Bao (aka CSharperMantle)
 * Really simple non-jQuery slider:
 *  https://codepen.io/CSharperMantle/pen/OJXLzVV
 *  MIT License. Copyright (c) Rong "Mantle" Bao (aka CSharperMantle) and Ben Wellby
 * Animated D2303 Class Flag:
 *  https://codepen.io/CSharperMantle/pen/MWeLxWY
 *  MIT License. Copyright (c) Rong "Mantle" Bao (aka CSharperMantle)
 * canvas-confetti:
 *  https://github.com/catdad/canvas-confetti
 *  ISC License. Copyright (c) 2020, Kiril Vatev
 */

(function () {
  const AsyncScriptLoader = {
    loadScript: function (url, baseElem, resolveWhen, isWithIntegrity, integrity, crossorigin) {
      return new Promise(function (resolve, reject) {
        const scriptElem = document.createElement('script')
        scriptElem.setAttribute('src', url)
        if (isWithIntegrity) {
          scriptElem.setAttribute('integrity', integrity)
          scriptElem.setAttribute('crossorigin', crossorigin)
        }
        scriptElem.addEventListener('load', function () {
          while (!resolveWhen());
          resolve()
        })
        scriptElem.addEventListener('error', function () {
          reject(new Error(`AsyncScriptLoader: ${url} fails to load`))
        })
        baseElem.insertAdjacentElement('afterbegin', scriptElem)
      })
    }
  }
  window.AsyncScriptLoader = AsyncScriptLoader
})();

(function () {
  // HACK: bypass script tag filtering, inserting tags for script, one linked by one, with promise chains
  const body = document.getElementsByTagName('body')[0]

  AsyncScriptLoader.loadScript('https://cdnjs.cloudflare.com/ajax/libs/jquery/3.5.1/jquery.min.js', body, () => {
    return (typeof $ !== 'undefined')
  },
  true, 'sha512-bLT0Qm9VnAYZDflyKcBaQ2gg0hSYNQrJ8RilYldYQ1FxQYoCLtUjuuRuZo+fjqhx/qtq/1itJ0C2ejDxltZVFg==', 'anonymous')
    .then(() => {
      return AsyncScriptLoader.loadScript('https://cdnjs.cloudflare.com/ajax/libs/lodash.js/4.17.20/lodash.min.js', body, () => {
        return (typeof _ === 'function')
      },
      true, 'sha512-90vH1Z83AJY9DmlWa8WkjkV79yfS2n2Oxhsi2dZbIv0nC4E6m5AbH8Nh156kkM7JePmqD6tcZsfad1ueoaovww==', 'anonymous')
    })
    .then(() => {
      return AsyncScriptLoader.loadScript('https://cdnjs.cloudflare.com/ajax/libs/gsap/3.5.1/gsap.min.js', body, () => {
        return (typeof gsap !== 'undefined')
      },
      false, null, null)
    })
    .then(() => {
      return AsyncScriptLoader.loadScript('https://cdn.jsdelivr.net/gh/CSharperMantle/CSharperMantle.github.io@HEAD/assets/js/CustomEase-3.5.1.min.js', body, () => {
        return (typeof CustomEase !== 'undefined')
      },
      false, null, null)
    })
    .then(() => {
      return AsyncScriptLoader.loadScript('https://cdn.jsdelivr.net/gh/CSharperMantle/CSharperMantle.github.io@HEAD/assets/js/CustomWiggle-3.4.3.min.js', body, () => {
        return (typeof CustomWiggle !== 'undefined')
      },
      false, null, null)
    })
    .then(() => {
      return AsyncScriptLoader.loadScript('https://cdn.jsdelivr.net/npm/canvas-confetti@1.3.2/dist/confetti.browser.min.js', body, () => {
        return (typeof confetti === 'function')
      },
      false, null, null)
    })
    .then(() => {
      loadDropper()
    })
    .catch((reason) => {
      console.log(reason)
    })
})()

const ELEMID_PRE_USER_AGENT = 'pre-user-agent'
const ELEMID_FIGURE_UNDER_CONSTRUCTION = 'figure-under-construction'
const ELEMID_H2_DEPRECATED_BANNER = 'h2-deprecated-banner'
const ELEMID_SCRIPT_ASTEROID = 'script-asteroid'
const ELEMID_SPAN_RANDOM_QUOTE = 'span-random-quote'
const SRC_SCRIPT_ASTEROID = 'https://cdn.jsdelivr.net/gh/CSharperMantle/CSharperMantle.github.io@HEAD/assets/js/asteroids.js'
const SRC_TXT_FORTUNE = 'https://cdn.jsdelivr.net/gh/CSharperMantle/CSharperMantle.github.io@HEAD/assets/txt/fortunes.txt'
let isDeprecatedBannerShowing = false;

// click-switching images
(function () {
  'use strict'

  function refreshSwitch (s) {
    const currentSwitch = s.dataset.switchCurrent

    const switchAttrStr = 'switchSrc-' + currentSwitch
    const currentSwitchSrc = s.dataset[switchAttrStr]

    s.setAttribute('src', currentSwitchSrc)
  }

  function switchNext (s) {
    let currentSwitch = parseInt(s.dataset.switchCurrent, 10)
    const switchCases = parseInt(s.dataset.switchCases, 10)

    currentSwitch += 1
    if (currentSwitch >= switchCases) {
      currentSwitch = 0
    }

    s.dataset.switchCurrent = currentSwitch
  }

  function initializeSwitch () {
    const switchables = document.getElementsByClassName('switchable')
    for (let i = 0; i < switchables.length; i += 1) {
      const switchable = switchables[i]
      refreshSwitch(switchable)
      switchable.addEventListener('click', () => {
        switchNext(switchable)
        refreshSwitch(switchable)
      })
    }
  }
  initializeSwitch()
})();

// non-jquery sliders
(function () {
  // ==GLOBAL VARS, CONSTS AND HELPERS==

  // create pager list items
  const sliderImagesList = document.querySelectorAll('.slider__images-image')
  const sliderPagersElem = document.querySelector('.js__slider__pagers') // we will only fill the first pager element

  // HACK: fill in sliders in advance in order to get the total count of elements in LAST_ELEM_INDEX
  function sliderPagePrefill () {
    sliderImagesList.forEach((image, index) => {
      const buttonElem = document.createElement('button')
      const buttonText = document.createTextNode(index + 1)
      buttonElem.appendChild(buttonText)
      buttonElem.setAttribute('type', 'button')
      sliderPagersElem.insertAdjacentElement('beforeend', buttonElem)

      // HACK: Chrome won't fire onload event for more than 1 time even the image's src has changed. This is to forcedly rerun the event handler each time the image is loaded. Chrome's behaviour is non-standard and described at http://code.google.com/p/chromium/issues/detail?id=7731#c12
      const imageLoader = new Image()
      imageLoader.addEventListener('load', () => {
        checkImageHeight()
        document.querySelector(SELECTOR_SLIDER_IMAGES).classList.add('loaded')
      })
      imageLoader.src = image.getAttribute('src')
    })
  }
  sliderPagePrefill()

  // set up constants and vars
  const SELECTOR_SLIDER_PAGERS = 'ol.js__slider__pagers button'
  const SELECTOR_SLIDER_PAGERS_ACTIVE = '.js__slider__pagers button.active'
  const SELECTOR_SLIDER_IMAGES = '.js__slider__images'
  const SELECTOR_SLIDER_IMAGES_ITEM = '.slider__images-item'
  const SELECTOR_SLIDER_CONTROL_NEXT = '.slider__control--next'
  const SELECTOR_SLIDER_CONTROL_PREV = '.slider__control--prev'

  // NOTE: You may be interested in tweaking switching speed by changing this constant.
  const SLIDER_SPEED = 5000

  const LAST_ELEM_INDEX =
    document.querySelectorAll(SELECTOR_SLIDER_PAGERS).length - 1

  let sliderTarget = null
  let animationOngoing = false // HACK: Prevent from interrupting animations
  let isDocumentOnFocus = true // HACK: Prevent the blurring from interrupting the animation

  function getFirstVisibleElem (iterable) {
    for (let i = 0; i < iterable.length; i++) {
      const elem = iterable[i]
      if (elem.style.display !== 'none' && elem.style.visibility !== 'hidden') {
        return elem
      }
    }
  }

  function indexOf (iterable, elem) {
    for (let i = 0; i < iterable.length; i++) {
      if (iterable[i] === elem) {
        return i
      }
    }
    return -1
  }

  function fadeInOut (elemFadeIn, elemFadeOut, speed) {
    animationOngoing = true
    const speed_ = speed || 20
    let currentInOpac = 0
    elemFadeIn.style.opacity = currentInOpac
    elemFadeOut.style.opacity = 1 - currentInOpac
    elemFadeIn.style.display = null
    elemFadeOut.style.display = null

    const interval = setInterval(() => {
      elemFadeIn.style.opacity = currentInOpac
      elemFadeOut.style.opacity = 1 - currentInOpac
      currentInOpac += 0.03
      if (currentInOpac >= 1) {
        elemFadeIn.style.opacity = null
        elemFadeOut.style.opacity = null
        elemFadeOut.style.display = 'none'
        clearInterval(interval)
        animationOngoing = false
      }
    }, speed_)
  }

  function initBlurDetection () {
    document.addEventListener('blur', () => {
      isDocumentOnFocus = false
    })
    document.addEventListener('focus', () => {
      isDocumentOnFocus = true
    })
  }
  initBlurDetection()

  // transition function
  function sliderResponse (sliderTarget) {
    const items = document.getElementsByClassName('slider__images-item')
    fadeInOut(items[sliderTarget], getFirstVisibleElem(items), 5)
    const pagers = document.querySelectorAll(SELECTOR_SLIDER_PAGERS)
    pagers.forEach((elem) => {
      elem.classList.remove('active')
    })
    pagers[sliderTarget].classList.add('active')
  }

  // add css height to slider images list
  function checkImageHeight () {
    const sliderHeight = getFirstVisibleElem(
      document.querySelectorAll('.slider__images-image')
    ).height
    document.querySelector(SELECTOR_SLIDER_IMAGES).style.height =
      sliderHeight + 'px'
  }

  // slider timing
  function sliderTiming () {
    if (!isDocumentOnFocus) {
      return
    }
    const currentActiveElem = document.querySelector(SELECTOR_SLIDER_PAGERS_ACTIVE)
    const currentActiveIndex = indexOf(
      currentActiveElem.parentElement.children,
      currentActiveElem
    )
    sliderTarget = currentActiveIndex
    sliderTarget = sliderTarget === LAST_ELEM_INDEX ? 0 : sliderTarget + 1
    sliderResponse(sliderTarget)
  }

  // ==SETUP FUNCTIONS==

  function initSliderPage () {
    window.onresize = () => {
      checkImageHeight()
    }
  }
  initSliderPage()

  // set up first slide
  function initFirstSlide () {
    document.querySelectorAll(SELECTOR_SLIDER_PAGERS)[0].classList.add('active')
    const slideImageItems = document.querySelectorAll(SELECTOR_SLIDER_IMAGES_ITEM)
    slideImageItems.forEach((elem) => {
      elem.style.display = 'none'
    })
    slideImageItems[0].style.display = null
  }
  initFirstSlide()

  // pager controls
  function initPageControl () {
    document
      .querySelectorAll(SELECTOR_SLIDER_PAGERS)
      .forEach((elem, currentIndex) => {
        elem.addEventListener('click', () => {
          if (!elem.classList.contains('active') && !animationOngoing) {
            sliderTarget = currentIndex
            sliderResponse(sliderTarget)
            resetTiming()
          }
        })
      })

    // next/prev controls
    document
      .querySelector(SELECTOR_SLIDER_CONTROL_NEXT)
      .addEventListener('click', () => {
        if (!animationOngoing) {
          const currentActiveElem = document.querySelector(
            SELECTOR_SLIDER_PAGERS_ACTIVE
          )
          const currentActiveIndex = indexOf(
            currentActiveElem.parentElement.children,
            currentActiveElem
          )
          sliderTarget = currentActiveIndex
          sliderTarget = sliderTarget === LAST_ELEM_INDEX ? 0 : sliderTarget + 1
          sliderResponse(sliderTarget)
          resetTiming()
        }
      })
    document
      .querySelector(SELECTOR_SLIDER_CONTROL_PREV)
      .addEventListener('click', () => {
        if (!animationOngoing) {
          const currentActiveElem = document.querySelector(
            SELECTOR_SLIDER_PAGERS_ACTIVE
          )
          const currentActiveIndex = indexOf(
            currentActiveElem.parentElement.children,
            currentActiveElem
          )
          sliderTarget = currentActiveIndex
          sliderTarget = sliderTarget === 0 ? LAST_ELEM_INDEX : sliderTarget - 1
          sliderResponse(sliderTarget)
          resetTiming()
        }
      })
  }
  initPageControl()

  // slider autoplay
  let timingRun = setInterval(() => {
    sliderTiming()
  }, SLIDER_SPEED)

  function resetTiming () {
    clearInterval(timingRun)
    timingRun = setInterval(() => {
      sliderTiming()
    }, SLIDER_SPEED)
  }
})()

// gsap animation
function loadDropper () {
  const select = (s) => document.querySelector(s)
  const mainSVG = select('.mainSVG')
  const liquid = select('#liquid')
  const flask = select('#flask')
  const confettiCanvas = select('#canvas-dropper-confetti')
  const pointArray = []
  const pointValueXArray = []
  const pointValueYArray = []
  const liquidWidth = 200
  const numPoints = 20
  const dripOffset = 0.0258
  const rippleAmount = '+=6'
  let startValX = 63
  const startValY = 115
  const colorArray = [
    '#E6098B',
    '#FFBE0B',
    '#FB5607',
    '#8338EC',
    '#3A86FF',
    '#51E5FF',
    '#04A777',
    '#F75C03',
    '#F71735'
  ]

  gsap.set(mainSVG, {
    visibility: 'visible'
  })
  gsap.set('.darkLiquid', {
    scaleX: -1,
    transformOrigin: '50% 50%'
  })
  for (let i = 0; i < numPoints; i++) {
    const p = liquid.points.appendItem(mainSVG.createSVGPoint())
    pointArray.push(p)
    pointValueXArray.push(
      i < numPoints - 2 ? startValX : i === numPoints - 2 ? 600 : 200
    )
    startValX += liquidWidth / (numPoints - 2)
    pointValueYArray.push(i < numPoints - 2 ? startValY : 800)
  }

  gsap.set(pointArray, {
    x: gsap.utils.wrap(pointValueXArray),
    y: gsap.utils.wrap(pointValueYArray)
  })

  gsap.set('#level', {
    transformOrigin: '50% 100%'
  })

  const makeDrip = () => {
    const currentColor = gsap.utils.random(colorArray)
    gsap.to(':root', {
      '--main-color': currentColor
    })

    const tl = gsap.timeline({
      defaults: {
        ease: CustomWiggle.create('', {
          type: 'easeOut',
          wiggles: gsap.utils.random(9, 12)
        })
      }
    })

    tl.fromTo(
      '#pipette1', {
        x: 250,
        opacity: 0
      }, {
        duration: 1,
        x: 160,
        opacity: 1,
        ease: 'expo.inOut'
      }
    )
      .fromTo(
        '#pipette1', {
          rotation: -95,
          transformOrigin: '50% 100%'
        }, {
          rotation: 0,
          transformOrigin: '50% 100%',
          duration: 1.5,
          ease: 'elastic(1.5, 0.83)'
        },
        0
      )
      .addLabel('pipetteReady')
      .fromTo(
        '#drip', {
          scale: 0
        }, {
          duration: 1,
          scale: 0.3,
          transformOrigin: '50% 0%',
          ease: 'elastic(1, 0.8)'
        }
      )
      .to(
        '#level', {
          duration: 1,
          scaleY: 0.2,
          ease: 'elastic(1, 0.8)'
        },
        'pipetteReady'
      )
      .fromTo(
        '#drip', {
          x: 165.5,
          y: 21
        }, {
          x: 165.5,
          y: 125,
          duration: 0.35,
          ease: 'power1.in'
        }
      )
      .addLabel('splash')
      .to(
        '.poly', {
          fill: currentColor,
          ease: 'sine'
        },
        'splash'
      )
      .to(
        pointArray, {
          duration: gsap.utils.random(3, 5),
          y: (i) => {
            return rippleAmount
          },
          stagger: {
            each: dripOffset,
            from: 'center'
          }
        },
        'splash'
      )
      .to(
        '#droplet', {
          duration: 0.23,
          y: 'random(-30, -60, 1)',
          rotation: 'random(20, 290)',
          ease: 'power1'
        },
        'splash'
      )
      .to(
        '#droplet', {
          duration: 0.23,
          y: 0,
          rotation: '+=30',
          ease: 'power1.in'
        },
        'splash+=0.23'
      )
      .fromTo(
        '#droplet', {
          scale: 1
        }, {
          duration: 0.23,
          scale: 0,
          transformOrigin: '50% 100%',
          ease: 'expo.in'
        },
        'splash+=0.23'
      )
      .to(
        '#level', {
          duration: 1,
          scaleY: 1,
          ease: 'expo.in'
        },
        'splash'
      )
      .to(
        '#pipette1', {
          duration: 1,
          rotation: 23,
          x: 100,
          opacity: 0,
          ease: 'expo.in'
        },
        'splash'
      )

    gsap.delayedCall(4, makeDrip)
  }

  makeDrip()

  // confetti
  const confettiInstance = confetti.create(confettiCanvas, {
    resize: true,
    useWorker: true
  })

  const createConfetti = _.throttle(() => {
    confettiInstance({
      particleCount: 100,
      spread: 100,
      startVelocity: 30
    })
  }, 500)

  flask.addEventListener('click', () => {
    createConfetti()
  })
};

// other interactive elements
(function () {
  'use strict'

  function getRandomInt (max) {
    return Math.floor(Math.random() * Math.floor(max))
  }

  document.getElementById(ELEMID_PRE_USER_AGENT).innerText = navigator.userAgent
  document.getElementById(ELEMID_FIGURE_UNDER_CONSTRUCTION).addEventListener('click', () => {
    const deprecatedBannerElem = document.getElementById(ELEMID_H2_DEPRECATED_BANNER)
    if (isDeprecatedBannerShowing) {
      // hide
      deprecatedBannerElem.setAttribute('hidden', '')
      isDeprecatedBannerShowing = false
      const asteroidScript = document.getElementById(ELEMID_SCRIPT_ASTEROID)
      document.body.removeChild(asteroidScript)
    } else {
      // show
      deprecatedBannerElem.removeAttribute('hidden')
      isDeprecatedBannerShowing = true
      const asteroidScript = document.createElement('script')
      asteroidScript.type = 'text/javascript'
      asteroidScript.setAttribute('id', ELEMID_SCRIPT_ASTEROID)
      document.body.appendChild(asteroidScript)
      asteroidScript.src = SRC_SCRIPT_ASTEROID
    }
  })
  // load fortune
  const fortuneXhr = new XMLHttpRequest()
  fortuneXhr.onload = () => {
    // fortune quotes are splitted with %
    const responseList = fortuneXhr.responseText.split('%')
    const randQuote = responseList[getRandomInt(responseList.length - 1)].trim()
    document.getElementById(ELEMID_SPAN_RANDOM_QUOTE).innerText = randQuote
  }
  fortuneXhr.open('GET', SRC_TXT_FORTUNE)
  fortuneXhr.send()
})()
