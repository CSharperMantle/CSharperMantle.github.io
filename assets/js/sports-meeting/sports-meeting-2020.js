/*
 * sports-meeting/sports-meeting-2020.js
 *
 * Libraries in use:
 *
 * async-script-loader:
 *  https://github.com/CSharperMantle/async-script-loader
 *  MIT License. Copyright (c) Rong "Mantle" Bao (aka CSharperMantle)
 * canvas-confetti:
 *  https://github.com/catdad/canvas-confetti
 *  ISC License. Copyright (c) 2020, Kiril Vatev
 * lodash:
 *  https://github.com/lodash/lodash/
 *  MIT License. Copyright JS Foundation and other contributors <https://js.foundation/>
 * jquery:
 *  https://jquery.com
 *  MIT License. Copyright OpenJS Foundation and other contributors, https://openjsf.org/
 * protonet-jquery.inview:
 *  https://github.com/protonet/jquery.inview
 *  WTFPL. Copyright (C) 2004 Sam Hocevar <sam@hocevar.net>
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

  AsyncScriptLoader.loadScript('https://cdnjs.cloudflare.com/ajax/libs/lodash.js/4.17.20/lodash.min.js', body, () => {
    return (typeof _ === 'function')
  },
  true, 'sha512-90vH1Z83AJY9DmlWa8WkjkV79yfS2n2Oxhsi2dZbIv0nC4E6m5AbH8Nh156kkM7JePmqD6tcZsfad1ueoaovww==', 'anonymous')
    .then(() => {
      return AsyncScriptLoader.loadScript('https://cdnjs.cloudflare.com/ajax/libs/jquery/3.5.1/jquery.min.js', body, () => {
        return (typeof jQuery !== 'undefined')
      },
      true, 'sha512-bLT0Qm9VnAYZDflyKcBaQ2gg0hSYNQrJ8RilYldYQ1FxQYoCLtUjuuRuZo+fjqhx/qtq/1itJ0C2ejDxltZVFg==', 'anonymous')
    })
    .then(() => {
      return AsyncScriptLoader.loadScript('https://cdnjs.cloudflare.com/ajax/libs/protonet-jquery.inview/1.1.2/jquery.inview.min.js', body, () => {
        return true
      },
      true, 'sha512-D68mBFX2aQwVh2wV6uCDLmabIveaSQL3uVUo2Ze7VwxIeOcAd4C1/JagkVoObb/NLkYDrdvY3JHK1KOfenHVcA==', 'anonymous')
    })
    .then(() => {
      return AsyncScriptLoader.loadScript('https://cdn.jsdelivr.net/npm/canvas-confetti@1.3.2/dist/confetti.browser.min.js', body, () => {
        return (typeof confetti === 'function')
      },
      false, null, null)
    })
    .then(() => {
      loadComponents()
    })
    .catch((reason) => {
      console.log(reason)
    })
})()

function loadComponents () {
  // confetti
  const confettiCanvas = document.getElementById('canvas-confetti-overlay')
  const confettiCount = 200
  const confettiDefaults = {
    origin: { y: 0.7 }
  }

  function fireConfettiIntern (instance, particleRatio, opts) {
    instance(Object.assign({}, confettiDefaults, opts, {
      particleCount: _.floor(confettiCount * particleRatio)
    }))
  }

  const confettiInstance = confetti.create(confettiCanvas, {
    resize: true,
    useWorker: true
  })

  const fireConfetti = function () {
    fireConfettiIntern(confettiInstance, 0.25, {
      spread: 26,
      startVelocity: 30
    })
    fireConfettiIntern(confettiInstance, 0.2, {
      spread: 60,
      startVelocity: 35
    })
    fireConfettiIntern(confettiInstance, 0.35, {
      spread: 100,
      decay: 0.91,
      scalar: 0.8,
      startVelocity: 40
    })
    fireConfettiIntern(confettiInstance, 0.1, {
      spread: 120,
      startVelocity: 15,
      decay: 0.92,
      scalar: 1.2
    })
    fireConfettiIntern(confettiInstance, 0.1, {
      spread: 120,
      startVelocity: 40
    })
  }

  $('#img-hidden-content:visible').on('inview', function (event, isInView) {
    if (isInView) {
      // element is now visible in the viewport
      fireConfetti()
    } else {
      // element has gone out of viewport
    }
  })
}