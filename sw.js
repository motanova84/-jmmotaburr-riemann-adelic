// Service Worker for Riemann Hypothesis Verification Dashboard
// Enables offline functionality for the static site

const CACHE_NAME = 'riemann-verification-v1';
const urlsToCache = [
  '/',
  '/index.html',
  '/riemann_viewer.html',
  '/public/zeros-sample.js',
  '/public/primes-sample.js', 
  '/public/validation-results.js',
  '/data/critical_line_verification.csv',
  '/data/mathematical_certificate.json'
];

// Install event - cache resources
self.addEventListener('install', (event) => {
  event.waitUntil(
    caches.open(CACHE_NAME)
      .then((cache) => {
        console.log('📦 Caching Riemann verification assets');
        return cache.addAll(urlsToCache);
      })
  );
});

// Fetch event - serve from cache when offline
self.addEventListener('fetch', (event) => {
  event.respondWith(
    caches.match(event.request)
      .then((response) => {
        // Return cached version or fetch from network
        return response || fetch(event.request);
      }
    )
  );
});

// Activate event - clean up old caches
self.addEventListener('activate', (event) => {
  event.waitUntil(
    caches.keys().then((cacheNames) => {
      return Promise.all(
        cacheNames.map((cacheName) => {
          if (cacheName !== CACHE_NAME) {
            console.log('🗑️ Deleting old cache:', cacheName);
            return caches.delete(cacheName);
          }
        })
      );
    })
  );
});